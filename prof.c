#include "all.h"

static Fn* fn;
// global RCon to _qbe_prof_edge, _qbe_prof_end
static Ref prof_edge_ref;
static Ref prof_end_ref;

static uint32_t edgehash(const char* bname, const char* sname) {
    const size_t n = strlen(fn->name) + strlen(bname) + strlen(sname);
    char filename[n + 1];
    strcpy(filename, sname);
    strcat(filename, bname);
    strcat(filename, fn->name);
    return hash(filename) % PROF_NEDGE;
}

static const char* edgename(const char* bname, const char* sname) {
    const size_t n = strlen("_prof_") + strlen(bname) + strlen("_") + strlen(sname);
    char* name = emalloc(n + 1);
    strcat(name, "_prof_");
    strcat(name, bname);
    strcat(name, "_");
    strcat(name, sname);
    name[n] = '\0';
    return name;
}

static Blk* edgesplit(const Blk* const blk, Blk* const succ) {
    assert(blk->jmp.type == Jjnz);

    Blk* s = newblk();
    s->id = fn->nblk++;

    // name
    strncpy(s->name, edgename(blk->name, succ->name), sizeof s->name);

    // instructions just call _qbe_prof_edge(edge_hash)
    s->nins = 2;
    s->ins = vnew(2, sizeof s->ins[0], PFn);

    Con edge = {
        .type = CBits,
        .bits.i = edgehash(blk->name, succ->name)
    };

    s->ins[0] = (Ins){
        .op = Oarg,
        .cls = KINT,
        .to = R,
        .arg = {newcon(&edge, fn), R}
    };

    s->ins[1] = (Ins){
        .op = Ocall,
        .cls = 0,
        .to = R,
        .arg = {prof_edge_ref, R}
    };

    // jmp to succ afterwards
    s->jmp.type = Jjmp;
    s->jmp.arg = R;
    s->s1 = succ;
    s->s1prob = 1.0f;

    return s;
}

// fixup phis after do_instrument()
static void fixphis() {
    for (const Blk* blk = fn->start; blk; blk = blk->link) {
        for (const Phi* phi = blk->phi; phi; phi = phi->link) {
            for (int a = 0; a < phi->narg; ++a) {
                const Blk* pred = phi->blk[a];
                if (pred->visit != 0) {
                    assert(pred->s1->s2 == NULL);
                    assert(pred->s2->s2 == NULL);
                    if (pred->s1->s1 == blk) { phi->blk[a] = pred->s1; }
                    if (pred->s2->s1 == blk) { phi->blk[a] = pred->s2; }
                }
            }
        }
    }
}

static void do_instrument() {
    Blk* last = NULL;

    for (Blk* blk = fn->start; blk; blk = blk->link) {
        last = blk;
        if (blk->jmp.type == Jjmp) {
            blk->s1prob = 1.0f;
            continue;
        }

        if (blk->jmp.type != Jjnz) { continue; }

        Blk* s1 = edgesplit(blk, blk->s1);
        Blk* s2 = edgesplit(blk, blk->s2);

        blk->s1 = s1;
        blk->s1prob = 0.5f;
        blk->s2 = s2;
        blk->s2prob = 0.5f;

        s2->link = blk->link;
        blk->link = s1;
        s1->link = s2;

        // this block will need fixing of phis later
        blk->visit = 1;
    }

    // if globally visible function main, then inject call _qbe_prof_end()
    if (strcmp(fn->name, "main") == 0 && fn->lnk.export) {
        assert(last != NULL);
        idup(last, last->ins, last->nins + 1);
        last->ins[last->nins - 1] = (Ins){
            .op = Ocall,
            .cls = 0,
            .to = R,
            .arg = {prof_end_ref, R}
        };
    }

    fixphis();
}

static void do_profile() {
    uint32_t edge_counts[PROF_NEDGE];

    size_t x = fread(edge_counts, sizeof edge_counts[0], PROF_NEDGE, fprof);
    if (x != PROF_NEDGE) {
        fprintf(stderr, "invalid read from prof.out\n");
        exit(1);
    }

    for (Blk* blk = fn->start; blk; blk = blk->link) {
        if (blk->jmp.type == Jjmp) { blk->s1prob = 1.0f; }
        if (blk->jmp.type == Jjnz) {
            const uint32_t s1n = edge_counts[edgehash(blk->name, blk->s1->name)];
            const uint32_t s2n = edge_counts[edgehash(blk->name, blk->s2->name)];
            blk->s1prob = (float) s1n / (s1n + s2n);
            blk->s2prob = 1.0f - blk->s1prob;
        }
    }

    if (debug['O']) {
        fprintf(stderr, "\n> Profiler info:\n");

        for (const Blk* blk = fn->start; blk; blk = blk->link) {
            if (blk->jmp.type != Jjnz) { continue; }

            const uint32_t s1n = edge_counts[edgehash(blk->name, blk->s1->name)];
            const uint32_t s2n = edge_counts[edgehash(blk->name, blk->s2->name)];
            fprintf(stderr, ">>%s: (%d, %d)\n", blk->name, s1n, s2n);
        }
    }
}

// breaks rpo, dom
void profile(Fn* const fn_) {
    fn = fn_;

    Con prof_edge_con = {
        .type = CAddr,
        .sym.id = intern("_qbe_prof_edge")
    };

    Con prof_end_con = {
        .type = CAddr,
        .sym.id = intern("_qbe_prof_end")
    };

    prof_edge_ref = newcon(&prof_edge_con, fn);
    prof_end_ref = newcon(&prof_end_con, fn);

    for (Blk* blk = fn->start; blk; blk = blk->link) {
        blk->visit = 0;
    }

    if (instrument) {
        do_instrument();
    } else if (profiled) {
        do_profile();
    }
}
