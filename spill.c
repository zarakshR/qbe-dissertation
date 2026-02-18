#include <time.h>

#include "all.h"

static void
aggreg(Blk* hd, Blk* b) {
    /* aggregate looping information at
     * loop headers */
    bsunion(hd->gen, b->gen);
    for (int k = 0; k < 2; k++)
        if (b->nlive[k] > hd->nlive[k])
            hd->nlive[k] = b->nlive[k];
}

// for all tmps involved in the reference, update their `nuse`, `ndef`, `cost`
static void
tmpuse(Ref r, int use, int loop, Fn* fn) {
    if (rtype(r) == RMem) {
        Mem* m = &fn->mem[r.val];
        tmpuse(m->base, 1, loop, fn);
        tmpuse(m->index, 1, loop, fn);
    } else if (rtype(r) == RTmp && r.val >= Tmp0) {
        Tmp* t = &fn->tmp[r.val];

        if (use) {
            t->nuse++;
        } else {
            t->ndef++;
        }

        t->cost += loop;
    }
}

/* evaluate spill costs of temporaries,
 * this also fills usage information
 * requires rpo, preds
 */
void
fillcost(Fn* fn) {
    // aggregate loop information in loop headers
    // for each loop header, set `gen` to total tmps generated in the entire loop and `nlive` to maximum live in at any loop block
    loopiter(fn, aggreg);

    if (debug['S']) {
        fprintf(stderr, "\n> Loop information:\n");
        for (Blk* b = fn->start; b; b = b->link) {
            uint a = 0;
            while (a < b->npred) {
                if (b->id <= b->pred[a]->id) { break; }
                a++;
            }
            if (a != b->npred) {
                fprintf(stderr, "\t%-10s", b->name);
                fprintf(stderr, " (%3d ", b->nlive[0]);
                fprintf(stderr, "%3d) ", b->nlive[1]);
                dumpts(b->gen, fn->tmp, stderr);
            }
        }
    }

    for (Tmp* t = fn->tmp; t - fn->tmp < fn->ntmp; t++) {
        // registers have max cost, never spill them
        t->cost = t - fn->tmp < Tmp0 ? UINT_MAX : 0;
        t->nuse = 0;
        t->ndef = 0;
    }

    // set loop costs for each tmp
    for (Blk* b = fn->start; b; b = b->link) {
        for (Phi* p = b->phi; p; p = p->link) {
            Tmp* dst = &fn->tmp[p->to.val];
            tmpuse(p->to, 0, 0, fn);
            // phi-defined tmps have sum of predecessors' loop costs added to them
            for (uint i = 0; i < p->narg; i++) {
                dst->cost += p->blk[i]->loop;
                tmpuse(p->arg[i], 1, p->blk[i]->loop, fn);
            }
        }

        for (Ins* i = b->ins; i < &b->ins[b->nins]; i++) {
            tmpuse(i->to, 0, b->loop, fn);
            tmpuse(i->arg[0], 1, b->loop, fn);
            tmpuse(i->arg[1], 1, b->loop, fn);
        }
        tmpuse(b->jmp.arg, 1, b->loop, fn);
    }

    if (debug['S']) {
        fprintf(stderr, "\n> Spill costs:\n");
        for (int i = Tmp0; i < fn->ntmp; i++) {
            fprintf(stderr, "\t%-10s %d\n", fn->tmp[i].name, fn->tmp[i].cost);
        }
        fprintf(stderr, "\n");
    }
}

static BSet* prefer; /* temps to prioritize in registers (for tcmp1) */
static Tmp* tmp; /* current temporaries (for tcmpX) */
static int ntmp; /* current # of temps (for limit) */
static int locs; /* stack size used by locals */
static int slot4; /* next slot of 4 bytes */
static int slot8; /* ditto, 8 bytes */
static NextUse* nu; // nextuse info.
static int off; // nextuse offset from current block
static BSet mask[2][1]; /* class masks */

// comparator to sort tmps by estimated distance, fallbacks to spill cost
static int
tcmp0(const void* pa, const void* pb) {
    const Tmp ta = tmp[*(int*) pa];
    const Tmp tb = tmp[*(int*) pb];

    const float ta_ed = nu[*(int*) pa].edbot + off;
    const float tb_ed = nu[*(int*) pb].edbot + off;

    // fallback to spill costs
    if (ta_ed == tb_ed) {
        return ta.cost < tb.cost ? 1 : -1;
    }

    return ta_ed > tb_ed ? 1 : -1;
}

static int
tcmp1(const void* pa, const void* pb) {
    const int ta = *(int*) pa;
    const int tb = *(int*) pb;

    if (bshas(prefer, ta) != bshas(prefer, tb)) {
        return bshas(prefer, ta) ? -1 : 1;
    }

    return tcmp0(pa, pb);
}

static Ref
slot(int t) {
    assert(t >= Tmp0 && "cannot spill register");
    int s = tmp[t].slot;

    // previously spilled
    if (s != -1) { return SLOT(s); }

    /* specific to NAlign == 3 */
    /* nice logic to pack stack slots
     * on demand, there can be only
     * one hole and slot4 points to it
     *
     * invariant: slot4 <= slot8
     */
    if (KWIDE(tmp[t].cls) == K64BIT) {
        s = slot8;
        if (slot4 == slot8)
            slot4 += 2;
        slot8 += 2;
    } else {
        s = slot4;
        if (slot4 == slot8) {
            slot8 += 2;
            slot4 += 1;
        } else {
            slot4 = slot8;
        }
    }

    s += locs;
    tmp[t].slot = s;

    return SLOT(s);
}

/* restricts b to hold at most k
 * temporaries, preferring those
 * present in f (if given), then
 * those with the largest spill
 * cost
 */
// TODO: each `limit` call must accept block and index into block instructions for est distance, ensure handling of jmp correctly
static void
limit(BSet* b, int k, BSet* f, NextUse* const blk_nu, int blk_off) {
    static int* tarr, maxt;
    int i, t;

    int nt = bscount(b);
    if (nt <= k) { return; }
    if (nt > maxt) {
        free(tarr);
        tarr = emalloc(nt * sizeof tarr[0]);
        maxt = nt;
    }
    for (i = 0, t = 0; bsiter(b, &t); t++) {
        bsclr(b, t);
        tarr[i++] = t;
    }
    if (nt > 1) {
        nu = blk_nu;
        off = blk_off;

        if (!f) {
            qsort(tarr, nt, sizeof tarr[0], tcmp0);
        } else {
            prefer = f;
            qsort(tarr, nt, sizeof tarr[0], tcmp1);
        }
    }
    for (i = 0; i < k && i < nt; i++) {
        bsset(b, tarr[i]);
    }
    for (; i < nt; i++) {
        slot(tarr[i]);
    }
}

/* spills temporaries to fit the
 * target limits using the same
 * preferences as limit(); assumes
 * that kint gprs and kflt fprs are
 * currently in use
 */
static void
limit2(BSet* b1, int kint, int kflt, BSet* f, const NextUse* const nu, const int off) {
    BSet b2[1];

    bsinit(b2, ntmp); /* todo, free those */
    bscopy(b2, b1);
    bsinter(b1, mask[KINT]);
    bsinter(b2, mask[KFLT]);
    limit(b1, T.ngpr - kint, f, nu, off);
    limit(b2, T.nfpr - kflt, f, nu, off);
    bsunion(b1, b2);
}

static void
sethint(BSet* u, bits r) {
    int t;

    for (t = Tmp0; bsiter(u, &t); t++)
        tmp[phicls(t, tmp)].hint.m |= r;
}

/* reloads temporaries in u that are
 * not in `live` from their slots
 */
static void
reloads(BSet* u, BSet* live) {
    int t;

    for (t = Tmp0; bsiter(u, &t); t++)
        if (!bshas(live, t))
            emit(Oload, tmp[t].cls, TMP(t), slot(t), R);
}

static void
storeifspilled(Ref r, int slot) {
    if (slot != -1) { emit(Ostorew + tmp[r.val].cls, 0, R, r, SLOT(slot)); }
}

static int
isregcpy(const Ins* i) {
    return i->op == Ocopy && isreg(i->arg[0]);
}

// handle parallel moves, returns first index `i` (going backwards) with a non regcpy instruction
static Ins*
dopm(const Blk* b, Ins* i, BSet* live) {
    BSet u[1];
    bits r;

    bsinit(u, ntmp); /* todo, free those */
    /* consecutive copies from
     * registers need to be handled
     * as one large instruction
     *
     * fixme: there is an assumption
     * that calls are always followed
     * by copy instructions here, this
     * might not be true if previous
     * passes change
     */
    Ins* i1 = ++i;
    do {
        i--;
        int t = i->to.val;
        if (!req(i->to, R)) {
            if (bshas(live, t)) {
                bsclr(live, t);
                storeifspilled(i->to, tmp[t].slot);
            }
        }
        bsset(live, i->arg[0].val);
    } while (i != b->ins && isregcpy(i - 1));

    bscopy(u, live);

    // TODO: (??) special handling for pmoves just after call to handle callconv and clobbering
    if (i != b->ins && (i - 1)->op == Ocall) {
        int n;
        live->t[0] &= ~T.retregs((i - 1)->arg[1], 0);
        limit2(live, T.nrsave[0], T.nrsave[1], 0, b->nextuse, i - b->ins);
        for (n = 0, r = 0; T.rsave[n] >= 0; n++)
            r |= BIT(T.rsave[n]);
        live->t[0] |= T.argregs((i - 1)->arg[1], 0);
    } else {
        limit2(live, 0, 0, 0, b->nextuse, i - b->ins);
        r = live->t[0];
    }
    sethint(live, r);
    reloads(u, live);
    do {
        emiti(*--i1);
    } while (i1 != i);

    return i;
}

static void
merge(BSet* live, const Blk* blk, BSet* s, const Blk* succ) {
    if (blk->loop <= succ->loop) {
        bsunion(live, s);
    } else {
        for (int t = 0; bsiter(s, &t); t++) {
            // if a phi-arg hasn't been spilled, keep it live
            if (tmp[t].slot == -1) { bsset(live, t); }
        }
    }
}

/* spill code insertion
 * requires spill costs, rpo, liveness
 *
 * Note: this will replace liveness
 * information (in, out) with temporaries
 * that must be in registers at block
 * borders
 *
 * Be careful with:
 * - Ocopy instructions to ensure register
 *   constraints
 */
void
spill(Fn* fn) {
    int lvarg[2];
    BSet live[1], u[1], w[1];

    tmp = fn->tmp;
    ntmp = fn->ntmp;

    bsinit(u, ntmp);
    bsinit(live, ntmp);
    bsinit(w, ntmp);
    bsinit(mask[KINT], ntmp); // masked int regs
    bsinit(mask[KFLT], ntmp); // masked flt regs

    locs = fn->slot;
    slot4 = 0;
    slot8 = 0;
    for (int t = 0; t < ntmp; t++) {
        if (t >= Tmp0) {
            bsset(mask[KBASE(tmp[t].cls)], t);
        } else if (t >= T.fpr0 && t < T.fpr0 + T.nfpr) {
            bsset(mask[KFLT], t);
        } else {
            bsset(mask[KINT], t);
        }
    }

    for (int n = fn->nblk - 1; n >= 0; n--) {
        Blk* const blk = fn->rpo[n];
        /* invariant: all blocks with bigger rpo got
         * their in,out updated. */

        /* 1. find temporaries in registers at
         * the end of the block (put them in live) */
        curi = 0;
        Blk* s1 = blk->s1;
        Blk* s2 = blk->s2;
        Blk* header = NULL;

        if (s1 && s1->id <= blk->id) { header = s1; }

        if (s2 && s2->id <= blk->id) {
            // s2 is the tighter loop header
            if (!header || s2->id >= header->id) { header = s2; }
        }

        // `live`, at each point, contains the tmps that need to be in registers
        bszero(live);

        if (header) {
            *header->gen->t |= T.rglob; /* don't spill globally live registers */
            for (int k = 0; k < 2; k++) {
                const int nreg = k == 0 ? T.ngpr : T.nfpr;
                bscopy(u, blk->out); // u = b->out
                bsinter(u, mask[k]); // u &= mask[k]
                bscopy(w, u); // w = u
                bsinter(u, header->gen); // u &= hd->gen
                bsdiff(w, header->gen); // w &= ~hd->gen

                if (bscount(u) < nreg) {
                    const int j = (int) bscount(w); /* live through */
                    const int l = header->nlive[k];
                    limit(w, nreg - (l - j), 0, blk->nextuse, 0);
                    bsunion(u, w);
                } else {
                    limit(u, nreg, 0, blk->nextuse, 0);
                }

                bsunion(live, u);
            }
        } else if (s1) {
            /* avoid reloading temporaries
             * in the middle of loops */
            liveon(w, blk, s1);
            merge(live, blk, w, s1);
            if (s2) {
                liveon(u, blk, s2);
                merge(live, blk, u, s2);
                bsinter(w, u); // w &= u
            }
            // prefer tmps that are phi args to (both) successors
            limit2(live, 0, 0, w, blk->nextuse, 0);
        } else {
            // exit block
            bscopy(live, blk->out);
            if (rtype(blk->jmp.arg) == RCall) {
                // if block ends in a call: add return register(s) to `live`
                *(live->t) |= T.retregs(blk->jmp.arg, 0);
            }
        }

        // assign slots for *tmps* without allocated registers
        for (int t = Tmp0; bsiter(blk->out, &t); t++) {
            if (!bshas(live, t)) {
                slot(t);
            }
        }

        // out will contain tmps that must be in registers at block end
        bscopy(blk->out, live);

        /* 2. process the block instructions */

        // WARNING: this branch is untested
        if (rtype(blk->jmp.arg) == RTmp) {
            // if jmp has tmp argument
            int t = blk->jmp.arg.val;
            assert(KBASE(tmp[t].cls) == KINT);
            lvarg[KINT] = bshas(live, t);
            bsset(live, t);
            bscopy(u, live);
            limit2(live, 0, 0, NULL, blk->nextuse, 0);
            if (!bshas(live, t)) {
                if (!lvarg[KINT]) {
                    bsclr(u, t);
                }
                blk->jmp.arg = slot(t);
            }
            reloads(u, live);
        }

        // spilling proceeds from end of block backwards
        curi = &insb[NIns];
        for (Ins* i = &blk->ins[blk->nins]; i != blk->ins;) {
            i--;

            // if is cpy from a reg, check for and handle parallel moves
            if (isregcpy(i)) {
                i = dopm(blk, i, live);
                continue;
            }

            // waiting regs, prefer these in `limit`
            bszero(w);

            if (rtype(i->to) == RTmp) {
                const int t = i->to.val;

                if (bshas(live, t)) {
                    bsclr(live, t);
                } else {
                    // put dst in want list; we want to have dst be in register if possible
                    assert(t >= Tmp0 && "dead reg");
                    bsset(live, t);
                    bsset(w, t);
                }
            }

            int j = T.memargs(i->op);

            if (rtype(i->arg[0]) == RMem) { j--; }
            if (rtype(i->arg[1]) == RMem) { j--; }
            // we must have `j` tmp arguments

            // for each arg, start live interval for each tmp used in arg
            for (int a = 0; a < 2; a++) {
                const Ref arg = i->arg[a];
                switch (rtype(arg)) {
                    case RMem:
                        const Mem* m = &fn->mem[arg.val];
                        if (rtype(m->base) == RTmp) {
                            bsset(live, m->base.val);
                            bsset(w, m->base.val);
                        }
                        if (rtype(m->index) == RTmp) {
                            bsset(live, m->index.val);
                            bsset(w, m->index.val);
                        }
                        break;
                    case RTmp:
                        // note if arg is live after this use
                        lvarg[a] = bshas(live, arg.val);
                        bsset(live, arg.val);
                        // TODO: (??) only the last tmp arg is hinted in `w`
                        if (j-- <= 0) { bsset(w, arg.val); }
                        break;
                    default: break;
                }
            }

            bscopy(u, live);
            limit2(live, 0, 0, w, blk->nextuse, i - blk->ins);

            for (int a = 0; a < 2; a++) {
                if (rtype(i->arg[a]) == RTmp) {
                    const int t = i->arg[a].val;
                    if (!bshas(live, t)) {
                        // do not reload if the argument is not live after this instruction
                        if (!lvarg[a]) {
                            bsclr(u, t);
                        }
                        i->arg[a] = slot(t);
                    }
                }
            }
            reloads(u, live);

            if (rtype(i->to) == RTmp) {
                int t = i->to.val;
                storeifspilled(i->to, tmp[t].slot);
                if (t >= Tmp0) {
                    /* in case i->to was a
                     * dead temporary */
                    bsclr(live, t);
                }
            }

            emiti(*i);
            bits r = *live->t; /* Tmp0 is NBit */
            sethint(live, r);
        }

        // no (physical) register must be live across a block boundary ...
        if (blk == fn->start) {
            // ... unless its the start block and they are clobbered in function
            assert(*live->t == (T.rglob | fn->reg));
        } else {
            assert(*live->t == T.rglob);
        }

        for (Phi* p = blk->phi; p; p = p->link) {
            assert(rtype(p->to) == RTmp);
            int t = p->to.val;
            if (bshas(live, t)) {
                bsclr(live, t);
                storeifspilled(p->to, tmp[t].slot);
            } else if (bshas(blk->in, t)) {
                /* only if the phi is live */
                p->to = slot(p->to.val);
            }
        }

        bscopy(blk->in, live);
        idup(blk, curi, &insb[NIns] - curi);
    }

    /* align the locals to a 16 byte boundary */
    /* specific to NAlign == 3 */
    slot8 += slot8 & 3;
    fn->slot += slot8;

    if (debug['S']) {
        fprintf(stderr, "\n> Block information:\n");
        for (Blk* b = fn->start; b; b = b->link) {
            fprintf(stderr, "\t%-10s (%5d) ", b->name, b->loop);
            dumpts(b->out, fn->tmp, stderr);
        }
        fprintf(stderr, "\n> After spilling:\n");
        printfn(fn, stderr);
    }
}
