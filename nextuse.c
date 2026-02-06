#include <math.h>

#include "all.h"

static const Fn* fn;

static int uses(const Ref r, int t) { // NOLINT(*-no-recursion)
    if (r.type == RTmp) {
        return r.val == t;
    }

    if (r.type == RMem) {
        return uses(fn->mem[r.val].base, t) || uses(fn->mem[r.val].index, t);
    }

    return 0;
}

static void fillusedefs(Blk* const blk) {
    for (const Phi* phi = blk->phi; phi; phi = phi->link) {
        for (uint i = 0; i < phi->narg; i++) {
            const Ref arg = phi->arg[i];
            if (arg.type == RTmp) { bsset(blk->uses, arg.val); }
        }

        const Ref to = phi->to;
        assert(to.type == RTmp);
        bsset(blk->defs, to.val);
    }

    for (const Ins* ins = blk->ins; ins < &blk->ins[blk->nins]; ins++) {
        for (int i = 0; i < 2; i++) {
            const Ref arg = ins->arg[i];
            if (arg.type == RTmp) { bsset(blk->uses, arg.val); }
        }

        const Ref to = ins->to;
        assert(to.type == RTmp);
        bsset(blk->defs, to.val);
    }
}

// ReSharper disable once CppNotAllPathsReturnValue
static float lptop(Blk* const blk, const int t) {
    if (!bshas(blk->uses, t) && !bshas(blk->defs, t)) { return blk->nextuse[t].lpbot; }

    switch (blk->nextuse[t].first) {
        case XXX:
            // do all phi args first
            for (const Phi* phi = blk->phi; phi; phi = phi->link) {
                int uses = 0;

                for (int i = 0; i < phi->narg; i++) {
                    const Ref arg = phi->arg[i];
                    uses = uses || (arg.type == RTmp && arg.val == t);
                }

                if (uses) {
                    blk->nextuse[t].first = NUUse;
                    blk->nextuse[t].fudist = 0;
                    return 1;
                }
            }

            for (const Phi* phi = blk->phi; phi; phi = phi->link) {
                if (phi->to.val == t) {
                    blk->nextuse[t].first = NUDef;
                    return 0;
                }
            }

            // search in body
            for (const Ins* ins = blk->ins; ins < &blk->ins[blk->nins]; ins++) {
                if (uses(ins->arg[0], t) || uses(ins->arg[1], t)) {
                    blk->nextuse[t].first = NUUse;
                    blk->nextuse[t].fudist = ins - blk->ins;
                    return 1;
                }

                if (ins->to.val == t) {
                    blk->nextuse[t].first = NUDef;
                    return 0;
                }
            }

            // no use or def found, but t in uses or defs
            die("unreachable");
        case NUDef:
            return 0;
        case NUUse:
            return 1;
    }
}

static float lpbot(Blk* const blk, const int t) {
    float lpbot = 0;

    if (blk->s1) {
        lpbot += blk->s1prob * blk->s1->nextuse[t].lptop;
    }

    if (blk->s2) {
        lpbot += blk->s2prob * blk->s2->nextuse[t].lptop;
    }

    return lpbot;
}

// ReSharper disable once CppNotAllPathsReturnValue
static float edtop(Blk* const blk, const int t) {
    if (blk->nextuse[t].lptop == 0) { return -1; }
    if (!bshas(blk->uses, t) && !bshas(blk->defs, t)) {
        return (blk->nextuse[t].edbot < 0) ? -1 : blk->nextuse[t].edbot + blk->nins;
    }

    switch (blk->nextuse[t].first) {
        case XXX:
            die("no liveprob info!");
        case NUDef:
            return -1;
        case NUUse:
            return blk->nextuse[t].fudist;
    }
}

static float edbot(Blk* const blk, const int t) {
    const float lpbot = blk->nextuse[t].lpbot;
    float edbot = 0;

    if (blk->s1) {
        const NextUse s1nu = blk->s1->nextuse[t];
        edbot += blk->s1prob * s1nu.edtop * s1nu.lptop;
    }

    if (blk->s2) {
        const NextUse s2nu = blk->s2->nextuse[t];
        edbot += blk->s2prob * s2nu.edtop * s2nu.lptop;
    }

    edbot = (lpbot == 0) ? -1 : edbot / lpbot;

    return edbot;
}

static int liveprobblk(Blk* const blk, const int ntmp) {
    int changed = 0;

    int count = 0; // TODO: remove
    for (int t = Tmp0; t < ntmp; t++) {
        const NextUse old = blk->nextuse[t];
        NextUse* const new = &blk->nextuse[t];

        new->lpbot = lpbot(blk, t);
        new->lptop = lptop(blk, t);

        if (fabsf(new->lptop - old.lptop) > 0.001f || fabsf(new->lpbot - old.lpbot) > 0.001f) { changed = 1; }
        count++;
    }

    return changed;
}

static int estdistblk(Blk* const blk, const int ntmp) {
    int changed = 0;

    int count = 0; // TODO: remove
    for (int t = Tmp0; t < ntmp; t++) {
        const NextUse old = blk->nextuse[t];
        NextUse* const new = &blk->nextuse[t];

        new->edbot = edbot(blk, t);
        new->edtop = edtop(blk, t);

        if (fabsf(new->edtop - old.edtop) > 0.001f || fabsf(new->edbot - old.edbot) > 0.001f) { changed = 1; }
        count++;
    }

    return changed;
}

// data-flow for live probability
static void doliveprob() {
    IList wl = ilnew(PFn);

    ilpush(&wl, fn->rpo[fn->nblk - 1]->id);
    while (wl.n > 0) {
        Blk* blk = fn->rpo[ilpop(&wl)];
        if (liveprobblk(blk, fn->ntmp)) {
            for (uint i = 0; i < blk->npred; i++) {
                ilpush(&wl, blk->pred[i]->id);
            }
        }
    }
}

// data-flow for estimated distances
static void doestdist() {
    IList wl = ilnew(PFn);

    ilpush(&wl, fn->rpo[fn->nblk - 1]->id);
    while (wl.n > 0) {
        Blk* blk = fn->rpo[ilpop(&wl)];
        if (estdistblk(blk, fn->ntmp)) {
            for (uint i = 0; i < blk->npred; i++) {
                ilpush(&wl, blk->pred[i]->id);
            }
        }
    }
}

void nextuse(const Fn* const fn_) {
    fn = fn_;

    for (Blk* blk = fn->start; blk; blk = blk->link) {
        bsinit(blk->uses, fn->ntmp);
        bsinit(blk->defs, fn->ntmp);
        blk->nextuse = emalloc(sizeof blk->nextuse[0] * fn->ntmp);

        // TODO: get branch probabilities from profiling info
        if (blk->s1 && blk->s2) {
            blk->s1prob = 0.5f;
            blk->s2prob = 0.5f;
        } else if (blk->s1) {
            blk->s1prob = 1;
        }

        fillusedefs(blk);
    }

    doliveprob();
    doestdist();

    if (debug['B']) {
        fprintf(stderr, "\n> Branch probability info:");

        for (const Blk* blk = fn->start; blk; blk = blk->link) {
            fprintf(stderr, "\n>>%s: <TNAME>: (LPTOP, EDTOP) (LPBOT, EDBOT)\n", blk->name);

            for (int t = Tmp0; t < fn->ntmp; t++) {
                const NextUse nu = blk->nextuse[t];
                fprintf(stderr, "%10s: (%f, %f) (%f, %f)\n", fn->tmp[t].name, nu.lptop, nu.edtop, nu.lpbot, nu.edbot);
            }
        }
    }
}
