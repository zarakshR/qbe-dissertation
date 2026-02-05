#include "all.h"

#ifdef TEST_PMOV
	#undef assert
	#define assert(x) assert_test(#x, x)
#endif

typedef struct RMap RMap;

struct RMap {
    // tmp `t[n]` is assigned to reg `r[n]`
    int t[Tmp0];
    int r[Tmp0];
    int w[Tmp0]; /* wait list, for unmatched hints */
    BSet mapped[1]; // bshas(mapped, t) if tmp `t` has mapping; bshas(mapped, r) if reg `r` already allocated
    int n; // no. of mappings in `t`/`r`
};

static bits regu; /* registers used */
static Tmp* tmp; /* function temporaries */
static Mem* mem; /* function mem references */
static struct {
    Ref src, dst;
    int cls;
} pm[Tmp0]; /* parallel move constructed */
static int npm; /* size of pm */
static int loop; /* current loop level */

static uint stmov; /* stats: added moves */
static uint stblk; /* stats: added blocks */

static int isgpr(const int r) {
    return r >= T.gpr0 && r < (T.gpr0 + T.ngpr);
}

static int isfpr(const int r) {
    return r >= T.fpr0 && r < (T.fpr0 + T.nfpr);
}

static int*
hint(int t) {
    return &tmp[phicls(t, tmp)].hint.r;
}

static void
sethint(int t, int r) {
    Tmp* p;
    p = &tmp[phicls(t, tmp)];
    if (p->hint.r == -1 || p->hint.w > loop) {
        p->hint.r = r;
        p->hint.w = loop;
        tmp[t].visit = -1;
    }
}

static void
rmapcpy(RMap* dst, RMap* src) {
    memcpy(dst->t, src->t, sizeof dst->t);
    memcpy(dst->r, src->r, sizeof dst->r);
    memcpy(dst->w, src->w, sizeof dst->w);
    bscopy(dst->mapped, src->mapped);
    dst->n = src->n;
}

// find register that tmp is mapped to (-1) otherwise
static int
rfind(RMap* map, int t) {
    for (int i = 0; i < map->n; i++) {
        if (map->t[i] == t) { return map->r[i]; }
    }

    return -1;
}

static Ref
rref(RMap* map, int t) {
    int r = rfind(map, t);

    if (r != -1) {
        return TMP(r);
    }

    assert(tmp[t].slot != -1 && "should have spilled");
    return SLOT(tmp[t].slot);
}

// map tmp `t` to reg `r`
static void
radd(RMap* map, int t, int r) {
    assert((t >= Tmp0 || t == r) && "invalid temporary");
    assert((isgpr(r) || isfpr(r)) && "invalid register");
    assert(!bshas(map->mapped, t) && "temporary has mapping");
    assert(!bshas(map->mapped, r) && "register already allocated");
    assert(map->n <= T.ngpr+T.nfpr && "too many mappings"); // NOTE: this may need to be a `<` instead of `<=`
    bsset(map->mapped, t);
    bsset(map->mapped, r);
    map->t[map->n] = t;
    map->r[map->n] = r;
    map->n++;
    regu |= BIT(r);
}

static Ref ralloctmp(RMap* const map, const int t, const int r) {
    radd(map, t, r);
    sethint(t, r);
    tmp[t].visit = r;
    int h = *hint(t);
    if (h != -1 && h != r) {
        map->w[h] = t;
    }

    return TMP(r);
}

static Ref
ralloctry(RMap* map, int t, int try) {
    // is register
    if (t < Tmp0) {
        assert(bshas(map->mapped, t));
        return TMP(t);
    }

    // already mapped
    if (bshas(map->mapped, t)) {
        int r = rfind(map, t);
        assert(r != -1);
        return TMP(r);
    }

    // last register allocated to this tmp
    int r = tmp[t].visit;

    // if none, or if currently allocated somewhere else, use hinted reg
    if (r == -1 || bshas(map->mapped, r)) {
        r = *hint(t);
    }

    // if no hint, or hinted reg currently allocated somewhere else
    if (r == -1 || bshas(map->mapped, r)) {
        if (try) {
            return R; // not allocated
        }

        bits avoid = tmp[phicls(t, tmp)].hint.m;
        avoid |= *map->mapped->t;

        int start, end;
        if (KBASE(tmp[t].cls) == KINT) {
            start = T.gpr0;
            end = start + T.ngpr;
        } else {
            start = T.fpr0;
            end = start + T.nfpr;
        }

        // try allocate reg that does not have avoid hint
        for (r = start; r < end; r++) {
            if (avoid && BIT(r)) { continue; }
            return ralloctmp(map, t, r);
        }

        // if none, try allocate reg that is not yet mapped
        for (r = start; r < end; r++) {
            if (bshas(map->mapped, r)) { continue; }
            return ralloctmp(map, t, r);
        }

        // else ran out of reisters
        die("no more regs");
    }

    return ralloctmp(map, t, r);
}

static inline Ref
ralloc(RMap* m, int t) {
    return ralloctry(m, t, 0);
}

static int
rfree(RMap* m, int t) {
    int i, r;

    assert(t >= Tmp0 || !(BIT(t) & T.rglob));
    if (!bshas(m->mapped, t))
        return -1;
    for (i = 0; m->t[i] != t; i++)
        assert(i+1 < m->n);
    r = m->r[i];
    bsclr(m->mapped, t);
    bsclr(m->mapped, r);
    m->n--;
    memmove(&m->t[i], &m->t[i + 1], (m->n - i) * sizeof m->t[0]);
    memmove(&m->r[i], &m->r[i + 1], (m->n - i) * sizeof m->r[0]);
    assert(t >= Tmp0 || t == r);
    return r;
}

static void
mdump(RMap* m) {
    int i;

    for (i = 0; i < m->n; i++)
        if (m->t[i] >= Tmp0)
            fprintf(
                stderr,
                " (%s, R%d)",
                tmp[m->t[i]].name,
                m->r[i]
            );
    fprintf(stderr, "\n");
}

static void
pmadd(Ref src, Ref dst, int k) {
    if (npm == Tmp0)
        die("cannot have more moves than registers");
    pm[npm].src = src;
    pm[npm].dst = dst;
    pm[npm].cls = k;
    npm++;
}

enum PMStat { ToMove, Moving, Moved };

static int
pmrec(enum PMStat* status, int i, int* k) {
    int j, c;

    /* note, this routine might emit
     * too many large instructions
     */
    if (req(pm[i].src, pm[i].dst)) {
        status[i] = Moved;
        return -1;
    }
    assert(KBASE(pm[i].cls) == KBASE(*k));
    assert((Kw|Kl) == Kl && (Ks|Kd) == Kd);
    *k |= pm[i].cls;
    for (j = 0; j < npm; j++)
        if (req(pm[j].dst, pm[i].src))
            break;
    switch (j == npm ? Moved : status[j]) {
        case Moving:
            c = j; /* start of cycle */
            emit(Oswap, *k, R, pm[i].src, pm[i].dst);
            break;
        case ToMove:
            status[i] = Moving;
            c = pmrec(status, j, k);
            if (c == i) {
                c = -1; /* end of cycle */
                break;
            }
            if (c != -1) {
                emit(Oswap, *k, R, pm[i].src, pm[i].dst);
                break;
            }
        /* fall through */
        case Moved:
            c = -1;
            emit(Ocopy, pm[i].cls, pm[i].dst, pm[i].src, R);
            break;
        default:
            die("unreachable");
    }
    status[i] = Moved;
    return c;
}

static void
pmgen() {
    int i;
    enum PMStat* status;

    status = alloc(npm * sizeof status[0]);
    assert(!npm || status[npm-1] == ToMove);
    for (i = 0; i < npm; i++)
        if (status[i] == ToMove)
            pmrec(status, i, (int[]){pm[i].cls});
}

static void
move(int r, Ref to, RMap* m) {
    int n, t, r1;

    r1 = req(to, R) ? -1 : rfree(m, to.val);
    if (bshas(m->mapped, r)) {
        /* r is used and not by to */
        assert(r1 != r);
        for (n = 0; m->r[n] != r; n++)
            assert(n+1 < m->n);
        t = m->t[n];
        rfree(m, t);
        bsset(m->mapped, r);
        ralloc(m, t);
        bsclr(m->mapped, r);
    }
    t = req(to, R) ? r : to.val;
    radd(m, t, r);
}

static int
isregcpy(Ins* i) {
    return i->op == Ocopy && isreg(i->arg[0]);
}

static Ins*
dopm(Blk* b, Ins* i, RMap* map) {
    RMap m0;
    int n, r, r1, t, s;
    Ins* i1,* ip;
    bits def;

    m0 = *map; /* okay since we don't use m0.b */
    m0.mapped->t = 0;
    i1 = ++i;
    do {
        i--;
        move(i->arg[0].val, i->to, map);
    } while (i != b->ins && isregcpy(i - 1));
    assert(m0.n <= map->n);
    if (i != b->ins && (i - 1)->op == Ocall) {
        def = T.retregs((i - 1)->arg[1], 0) | T.rglob;
        for (r = 0; T.rsave[r] >= 0; r++)
            if (!(BIT(T.rsave[r]) & def))
                move(T.rsave[r], R, map);
    }
    for (npm = 0, n = 0; n < map->n; n++) {
        t = map->t[n];
        s = tmp[t].slot;
        r1 = map->r[n];
        r = rfind(&m0, t);
        if (r != -1)
            pmadd(TMP(r1), TMP(r), tmp[t].cls);
        else if (s != -1)
            pmadd(TMP(r1), SLOT(s), tmp[t].cls);
    }
    for (ip = i; ip < i1; ip++) {
        if (!req(ip->to, R))
            rfree(map, ip->to.val);
        r = ip->arg[0].val;
        if (rfind(map, r) == -1)
            radd(map, r, r);
    }
    pmgen();
    return i;
}

// priority for return 1 if `r1` has higher priority else 0
static int
prio1(Ref r1, Ref r2) {
    /* trivial heuristic to begin with,
     * later we can use the distance to
     * the definition instruction
     */
    (void) r2;
    return *hint(r1.val) != -1;
}

static void
insert(Ref* r, Ref** rs, int p) {
    int i = p;

    rs[i] = r;
    while (i-- > 0 && prio1(*r, *rs[i])) {
        rs[i + 1] = rs[i];
        rs[i] = r;
    }
}

static void
doblk(Blk* b, RMap* cur) {
    int t, x, r, rf, rt, nr;
    bits rs;
    Ins* i,* i1;
    Mem* m;
    Ref* ra[4];

    if (rtype(b->jmp.arg) == RTmp)
        b->jmp.arg = ralloc(cur, b->jmp.arg.val);
    curi = &insb[NIns];
    for (i1 = &b->ins[b->nins]; i1 != b->ins;) {
        emiti(*--i1);
        i = curi;
        rf = -1;
        switch (i->op) {
            case Ocall:
                rs = T.argregs(i->arg[1], 0) | T.rglob;
                for (r = 0; T.rsave[r] >= 0; r++)
                    if (!(BIT(T.rsave[r]) & rs))
                        rfree(cur, T.rsave[r]);
                break;
            case Ocopy:
                if (isregcpy(i)) {
                    curi++;
                    i1 = dopm(b, i1, cur);
                    stmov += i + 1 - curi;
                    continue;
                }
                if (isreg(i->to))
                    if (rtype(i->arg[0]) == RTmp)
                        sethint(i->arg[0].val, i->to.val);
            /* fall through */
            default:
                if (!req(i->to, R)) {
                    assert(rtype(i->to) == RTmp);
                    r = i->to.val;
                    if (r < Tmp0 && (BIT(r) & T.rglob))
                        break;
                    rf = rfree(cur, r);
                    if (rf == -1) {
                        assert(!isreg(i->to));
                        curi++;
                        continue;
                    }
                    i->to = TMP(rf);
                }
                break;
        }

        // collect all tmp args used in instruction into `ra`
        for (x = 0, nr = 0; x < 2; x++) {
            switch (rtype(i->arg[x])) {
                case RMem:
                    m = &mem[i->arg[x].val];
                    if (rtype(m->base) == RTmp)
                        insert(&m->base, ra, nr++);
                    if (rtype(m->index) == RTmp)
                        insert(&m->index, ra, nr++);
                    break;
                case RTmp:
                    insert(&i->arg[x], ra, nr++);
                    break;
            }
        }

        for (r = 0; r < nr; r++) {
            *ra[r] = ralloc(cur, ra[r]->val);
        }

        // (??) why doesn't this skip `emit`?
        if (i->op == Ocopy && req(i->to, i->arg[0]))
            curi++;

        /* try to change the register of a hinted
         * temporary if rf is available */
        if (rf != -1 && (t = cur->w[rf]) != 0)
            if (!bshas(cur->mapped, rf) && *hint(t) == rf
                && (rt = rfree(cur, t)) != -1) {
                tmp[t].visit = -1;
                ralloc(cur, t);
                assert(bshas(cur->mapped, rf));
                emit(Ocopy, tmp[t].cls, TMP(rt), TMP(rf), R);
                stmov += 1;
                cur->w[rf] = 0;
                for (r = 0; r < nr; r++)
                    if (req(*ra[r], TMP(rt)))
                        *ra[r] = TMP(rf);
                /* one could iterate this logic with
                 * the newly freed rt, but in this case
                 * the above loop must be changed */
            }
    }
    idup(b, curi, &insb[NIns] - curi);
}

/* qsort() comparison function to peel loop nests from inside out */
static int
carve(const void* a, const void* b) {
    Blk* ba,* bb;

    /* todo, evaluate if this order is really
     * better than the simple postorder */
    ba = *(Blk**) a;
    bb = *(Blk**) b;
    if (ba->loop == bb->loop)
        return ba->id > bb->id ? -1 : ba->id < bb->id;
    return ba->loop > bb->loop ? -1 : +1;
}

/* comparison function to order temporaries
 * for allocation at the end of blocks */
// return > 0 if `t1` has more prio than `t2`
static int
prio2(int t1, int t2) {
    assert(tmp[t1].visit == -1 || tmp[t1].visit > 0);
    assert(tmp[t2].visit == -1 || tmp[t2].visit > 0);
    if ((tmp[t1].visit ^ tmp[t2].visit) < 0) /* != signs */
        return tmp[t1].visit != -1 ? +1 : -1;
    if ((*hint(t1) ^ *hint(t2)) < 0)
        return *hint(t1) != -1 ? +1 : -1;
    return tmp[t1].cost - tmp[t2].cost;
}

/* register allocation
 * depends on rpo, phi, cost, (and obviously spill)
 */
// pre-invariant: IR has no more live temporaries (at any program point) than there are machine registers
// at this point, liveness contains info about which temporaries must be in registers
// post-invariant, b->in contains tmps that have been assigned to registers
void
rega(Fn* fn) {
    // scratch data
    int j, t, r, x;
    uint u, n;

    // end[n]/beg[n] is the register mapping at the end/start of block n
    RMap* end,* beg;

    /* 1. setup */
    stmov = 0;
    stblk = 0;
    regu = 0;
    tmp = fn->tmp;
    mem = fn->mem;
    end = alloc(fn->nblk * sizeof end[0]);
    beg = alloc(fn->nblk * sizeof beg[0]);
    for (n = 0; n < fn->nblk; n++) {
        bsinit(end[n].mapped, fn->ntmp);
        bsinit(beg[n].mapped, fn->ntmp);
    }

    loop = INT_MAX;
    for (t = 0; t < fn->ntmp; t++) {
        tmp[t].hint.r = t < Tmp0 ? t : -1;
        tmp[t].hint.w = loop;
        tmp[t].visit = -1;
    }

    Blk** blk = alloc(fn->nblk * sizeof blk[0]);
    // initialize `blk` array from `b` linked list; `blk` will contain blocks in program order
    {
        int i = 0;
        for (Blk* b = fn->start; b; b = b->link) { blk[i++] = b; }
    }

    // sort blocks by loop nesting-depth; most nested loop first
    qsort(blk, fn->nblk, sizeof blk[0], carve);

    // fprintf(stderr, "tmps: %d\n", fn->ntmp);
    {
        // Blk* b;
        // for (b = fn->start; b; b = b->link) {
        //     fprintf(stderr, "%s (%p, %p)", b->name, b->s1, b->s2);
        //     fprintf(stderr, "\n");
        // }
    }

    // process register hints (for loading from parameters into locals)
    // register hints are listed first in the function body (i.e., in fn->start) as copy instructions
    // i.e., any `%t =_ copy %p` at the start of the function is a hint to use same register for `t` as for `p`
    for (uint i = 0; i < fn->start->nins; i++) {
        Ins ins = fn->start->ins[i];
        // hints are always copies from reg to reg
        if (ins.op != Ocopy || !isreg(ins.arg[0])) { break; }
        assert(rtype(ins.to) == RTmp);
        // hint that the dst should use same register as the src
        sethint(ins.to.val, ins.arg[0].val);
    }

    /* 2. allocate registers starting from block end */
    for (uint i = 0; i < fn->nblk; i++) {
        Blk* b = blk[i];
        loop = b->loop;

        // zero initialize `cur`
        RMap cur;
        bsinit(cur.mapped, fn->ntmp);
        cur.n = 0;
        bszero(cur.mapped);
        memset(cur.w, 0, sizeof cur.w);

        // `rl` 0 .. `x` inclusive contains tmps that must be in registers (post-spill invariant)
        int rl[Tmp0];

        // `x` tracks total number of registers allocated so far
        for (x = 0, t = Tmp0; bsiter(b->out, &t); t++) {
            j = x++;
            rl[j] = t;
            // bubble `t` down to its correct spot
            while (j-- > 0 && prio2(t, rl[j]) > 0) {
                rl[j + 1] = rl[j];
                rl[j] = t;
            }
        }

        // (??) registers are mapped to themselves
        for (r = 0; bsiter(b->out, &r) && r < Tmp0; r++) { radd(&cur, r, r); }

        // for each assigned register, allocate a register
        for (j = 0; j < x; j++) { ralloctry(&cur, rl[j], 1); }
        for (j = 0; j < x; j++) { ralloc(&cur, rl[j]); }

        // end <- cur
        rmapcpy(&end[b->id], &cur);

        doblk(b, &cur);
        bscopy(b->in, cur.mapped);

        // remove any tmps defined by phis from `b->in`
        for (Phi* p = b->phi; p; p = p->link) {
            if (rtype(p->to) == RTmp) { bsclr(b->in, p->to.val); }
        }

        // beg <- cur
        rmapcpy(&beg[b->id], &cur);
    }

    /* 3. emit copies shared by multiple edges
     * to the same block */
    // for each block `s` in program order
    for (Blk* b = fn->start; b; b = b->link) {
        // only consider blocks with multiple predecessors
        if (b->npred <= 1) { continue; }

        RMap* map = &beg[b->id];

        /* rl maps a register that is live at the
         * beginning of b to the one used in all
         * predecessors (if any, -1 otherwise) */
        int rl[Tmp0] = {0};

        /* to find the register of a phi in a
         * predecessor, we have to find the
         * corresponding argument */
        for (Phi* p = b->phi; p; p = p->link) {
            if (rtype(p->to) != RTmp || (r = rfind(map, p->to.val)) == -1) { continue; }

            for (u = 0; u < p->narg; u++) {
                Blk* srcblk = p->blk[u];
                Ref src = p->arg[u];
                if (rtype(src) != RTmp) { continue; }
                x = rfind(&end[srcblk->id], src.val);
                if (x == -1) {
                    /* spilled */
                    continue;
                }
                rl[r] = (!rl[r] || rl[r] == x) ? x : -1;
            }
            if (rl[r] == 0) { rl[r] = -1; }
        }

        /* process non-phis temporaries */
        for (j = 0; j < map->n; j++) {
            t = map->t[j];
            r = map->r[j];
            if (rl[r] || t < Tmp0 /* todo, remove this */) { continue; }
            for (Blk** pred = b->pred; pred < &b->pred[b->npred]; pred++) {
                x = rfind(&end[(*pred)->id], t);
                if (x == -1) /* spilled */
                    continue;
                rl[r] = (!rl[r] || rl[r] == x) ? x : -1;
            }
            if (rl[r] == 0) { rl[r] = -1; }
        }

        npm = 0;
        for (j = 0; j < map->n; j++) {
            t = map->t[j];
            r = map->r[j];
            x = rl[r];
            assert(x != 0 || t < Tmp0 /* todo, ditto */);
            if (x != -1 && !bshas(map->mapped, x)) {
                pmadd(TMP(x), TMP(r), tmp[t].cls);
                map->r[j] = x;
                bsset(map->mapped, x);
            }
        }
        curi = &insb[NIns];
        pmgen();
        j = &insb[NIns] - curi;
        if (j == 0) { continue; }
        stmov += j;
        b->nins += j;
        Ins* ins = alloc(b->nins * sizeof(Ins));
        icpy(icpy(ins, curi, j), b->ins, b->nins - j);
        b->ins = ins;
    }

    if (debug['R']) {
        fprintf(stderr, "\n> Register mappings:\n");
        for (n = 0; n < fn->nblk; n++) {
            Blk* b = fn->rpo[n];
            fprintf(stderr, "\t%-10s beg", b->name);
            mdump(&beg[n]);
            fprintf(stderr, "\t           end");
            mdump(&end[n]);
        }
        fprintf(stderr, "\n");
    }

    /* 4. emit remaining copies in new blocks */
    // for each block `b` in program-order
    Blk* blist = 0;
    for (Blk* b = fn->start; /* */ ; b = b->link) {
        Blk*** succs = (Blk**[3]){&b->s1, &b->s2, (Blk*[1]){0}};

        succs--;
        while (**++succs) {
            Blk* s = **succs;
            npm = 0;
            for (Phi* p = s->phi; p; p = p->link) {
                Ref dst = p->to;
                assert(rtype(dst)==RSlot || rtype(dst)==RTmp);
                if (rtype(dst) == RTmp) {
                    r = rfind(&beg[s->id], dst.val);
                    if (r == -1) { continue; }
                    dst = TMP(r);
                }
                for (u = 0; p->blk[u] != b; u++) { assert(u+1 < p->narg); }
                Ref src = p->arg[u];
                if (rtype(src) == RTmp) { src = rref(&end[b->id], src.val); }
                pmadd(src, dst, p->cls);
            }
            for (t = Tmp0; bsiter(s->in, &t); t++) {
                Ref src = rref(&end[b->id], t);
                Ref dst = rref(&beg[s->id], t);
                pmadd(src, dst, tmp[t].cls);
            }
            curi = &insb[NIns];
            pmgen();
            if (curi == &insb[NIns]) { continue; }
            Blk* new = newblk();
            new->loop = (b->loop + s->loop) / 2;
            new->link = blist;
            blist = new;
            fn->nblk++;
            strf(new->name, "%s_%s", b->name, s->name);
            stmov += &insb[NIns] - curi;
            stblk += 1;
            idup(new, curi, &insb[NIns] - curi);
            new->jmp.type = Jjmp;
            new->s1 = s;
            **succs = new;
        }

        if (!b->link) {
            b->link = blist;
            break;
        }
    }

    // destroy all phis
    for (Blk* b = fn->start; b; b = b->link) { b->phi = 0; }

    // set registers used
    fn->reg = regu;

    if (debug['R']) {
        fprintf(stderr, "\n> Register allocation statistics:\n");
        fprintf(stderr, "\tnew moves:  %d\n", stmov);
        fprintf(stderr, "\tnew blocks: %d\n", stblk);
        fprintf(stderr, "\n> After register allocation:\n");
        printfn(fn, stderr);
    }
}
