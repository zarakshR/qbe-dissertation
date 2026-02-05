#include "all.h"

#include <math.h>
#include <signal.h>

// TODO: a phi shouldn't count as a 0 distance use, use phi representatives
void initnextuse(Blk* const blk) {
    for (const Phi* phi = blk->phi; phi; phi = phi->link) {
        assert(rtype(phi->to) == RTmp);

        // phi args
        for (uint i = 0; i < phi->narg; i++) {
            if (rtype(phi->arg[i]) == RTmp) {
                bsset(blk->uses, phi->arg[i].val);
                blk->nextuse[phi->arg[i].val].lptop = 1;
                blk->nextuse[phi->arg[i].val].dist = 0;
                blk->nextuse[phi->arg[i].val].edtop = 0;
            }
        }

        // phi def: a phi-defined tmp can have itself as an argument
        if (!bshas(blk->uses, phi->to.val)) {
            bsset(blk->defs, phi->to.val);
            blk->nextuse[phi->to.val].lptop = 0;
            blk->nextuse[phi->to.val].edtop = -1;
            blk->nextuse[phi->to.val].dist = -1;
        }
    }

    for (const Ins* ins = blk->ins; ins < &blk->ins[blk->nins]; ins++) {
        // can only ever be one def
        if (rtype(ins->to) == RTmp && !bshas(blk->uses, ins->to.val)) {
            bsset(blk->defs, ins->to.val);
            blk->nextuse[ins->to.val].lptop = 0;
            blk->nextuse[ins->to.val].edtop = -1;
            blk->nextuse[ins->to.val].dist = -1;
        }

        // mark args as uses
        for (int a = 0; a < 2; a++) {
            const Ref arg = ins->arg[a];

            if (rtype(arg) != RTmp) { continue; }
            if (bshas(blk->uses, arg.val) || bshas(blk->defs, arg.val)) { continue; }

            bsset(blk->uses, arg.val);
            blk->nextuse[arg.val].lptop = 1;
            blk->nextuse[arg.val].edtop = ins - blk->ins;
            blk->nextuse[arg.val].dist = ins - blk->ins;
        }
    }

    for (int t = 0; bsiter(blk->out, &t); t++) {
        if (bshas(blk->uses, t) || bshas(blk->defs, t)) { continue; }
        blk->nextuse[t].lpbot = 1;
        blk->nextuse[t].edtop = blk->nins;
    }

    for (int t = 0; bsiter(blk->in, &t); t++) {
        if (bshas(blk->uses, t) || bshas(blk->defs, t)) { continue; }
        blk->nextuse[t].lptop = 1;
        blk->nextuse[t].edtop = blk->nins;
    }

    if (blk->s1 && blk->s2) {
        blk->s1prob = 0.5f;
        blk->s2prob = 0.5f;
    } else if (blk->s1) {
        blk->s1prob = 1;
    }
}

int donextuse(const int ntmp, Blk* const blk) {
    int changed = 0;

    for (int i = Tmp0; i < ntmp; i++) {
        const NextUse old = blk->nextuse[i];
        NextUse* new = &blk->nextuse[i];

        float lpbot = 0;
        if (blk->s1) {
            lpbot += blk->s1prob * blk->s1->nextuse[i].lptop;
        }
        if (blk->s2) {
            lpbot += blk->s2prob * blk->s2->nextuse[i].lptop;
        }

        float edbot = 0;
        if (blk->s1) {
            edbot += blk->s1prob * blk->s1->nextuse[i].edtop * blk->s1->nextuse[i].lptop;
        }
        if (blk->s2) {
            edbot += blk->s2prob * blk->s2->nextuse[i].edtop * blk->s2->nextuse[i].lptop;
        }
        // if t not live at bottom of block, then expected distance is infinite
        edbot = (lpbot == 0) ? -1 : edbot / (lpbot * lpbot);

        new->edbot = edbot;
        new->edtop = (new->lptop == 0.0) ? -1 : (old.dist != -1 && bshas(blk->uses, i)) ? old.dist : edbot + blk->nins;
        new->lpbot = lpbot;
        new->lptop = bshas(blk->defs, i) ? 0 : bshas(blk->uses, i) ? 1 : lpbot;

        changed = changed || new->edtop != old.edtop || new->edbot != old.edbot || new->lptop != old.lptop || new->lpbot != old.
                  lpbot;
    }

    return changed;
}

void nextuse(const Fn* const fn) {
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        bsinit(blk->uses, fn->ntmp);
        bsinit(blk->defs, fn->ntmp);
        blk->nextuse = emalloc(sizeof blk->nextuse[0] * fn->ntmp);

        for (int i = 0; i < fn->ntmp; i++) {
            blk->nextuse[i].edtop = -1;
        }

        initnextuse(blk);
    }

    int changed;
    do {
        changed = 0;
        for (int i = 0; i < fn->nblk; i++) {
            changed = changed || donextuse(fn->ntmp, fn->rpo[i]);
        }
    } while (changed);
        }
    }
}
