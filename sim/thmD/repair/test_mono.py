"""Lemma R / Lemma N with the monotone I_l (every edge incised at a level below l, as in [18, Def. 3.2]).

usage: python3 -I test_mono.py RULE START COUNT [size grid]
At every 'fixed' level of the sim/thmD driver, Definition R is rebuilt with
I_mono = P + every P_i' passed to thmD.incise so far, and checked with test_repair.check_level
(Euler for Table R, property 1 vs pieces, property 2, Fact N + closedness vs live annuli, distances,
copies, Rule M vs previous level). Extra checks (Lemma N in full):
  - G*_l (pieces + pairs) has the live annuli as connected components; G*_1 is connected;
  - every level-l piece refines one level-(l-1) piece under x -> parent token (all pieces);
  - Rule M for every piece, residual ones included.
"""
import sys, os, collections, json, time, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import test_repair as T
thmD, FGm = T.thmD, T.FGm

EVER = set()
ORIG_INC = thmD.incise


def inc_wrapped(ctx, A, Qn, Qe):
    for (la, lb) in Qe:
        EVER.add(la[0] >> 1)
    return ORIG_INC(ctx, A, Qn, Qe)


thmD.incise = inc_wrapped
C = collections.Counter()
NOTES = []
PREV = {}


def bad(k, v):
    C['BAD_' + k] += 1
    if len(NOTES) < 20:
        NOTES.append((k, str(v)[:300]))


def comps(pcs, toks):
    t2p = {x: i for i, (_, _, seq) in enumerate(pcs) for x in seq}
    par = list(range(len(pcs)))

    def fd(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    for x in toks:
        a, b = fd(t2p[x]), fd(t2p[FGm.partner(x)])
        par[a] = b
    return t2p, [fd(i) for i in range(len(pcs))]


def extra_checks(emb, Gf, annuli, level, prev):
    pcs = FGm.pieces(emb, Gf)
    t2p, comp = comps(pcs, Gf.toks)
    if level == 1 and len(set(comp)) != 1:
        bad('G1_disconnected', len(set(comp)))
    # live annuli are whole components
    for A in annuli:
        ps = {t2p[x] for X in A.nodes.values() for x in X.seq}
        cs = {comp[p] for p in ps}
        if len(cs) != 1:
            bad('annulus_spans_components', (level, A.aid))
            continue
        c = cs.pop()
        if {i for i in range(len(pcs)) if comp[i] == c} != ps:
            bad('annulus_not_whole_component', (level, A.aid))
        C['annuli_checked'] += 1
        C['nodeparts_checked'] += len(A.nodes)
    C['residual_components'] += len(set(comp)) - len(annuli)
    # refinement and Rule M for every piece
    vpiece = {}
    for (a, b, typ, info, h) in Gf.E:
        if typ == 'R':
            vpiece[a] = vpiece[b] = t2p[info]
    if prev is not None:
        palpha, pbeta, pI, pt2p, pvpiece = prev
        for i, (f, cyc, seq) in enumerate(pcs):
            par = set()
            for x in seq:
                d, l = x
                xp = x if (d >> 1) in pI else (d, 0)
                if xp not in pt2p:
                    bad('parent_token_missing', (level, x))
                    continue
                par.add(pt2p[xp])
                for w in (emb.tl[d], emb.tl[d ^ 1]):
                    ap = palpha[xp] if emb.tl[d] == w else pbeta[xp]
                    if pvpiece.get(ap) != pt2p[xp]:
                        bad('ruleM_att_not_on_parent', (level, x, w))
            if len(par) != 1:
                bad('piece_not_refining', (level, i, par))
            C['pieces_refine_ok'] += 1
    return (Gf.alpha, Gf.beta, set(Gf.I), t2p, vpiece)


def wrapped(emb, incised, epts, variant='literal'):
    Gc = T.ORIG_BUILD(emb, incised, epts, variant)
    if variant != 'fixed':
        return Gc
    fr = sys._getframe(1).f_locals
    if 'active' in fr and 'A1' in fr:
        annuli, level = list(fr['active']), fr.get('level')
    else:
        annuli, level = [fr['A0']], 0
        T.STATE.clear()
        T.STATE['prev'] = None
        T.STATE['prevI'] = None
        PREV.clear()
        PREV['prev'] = None
    Imono = set(incised) | EVER
    if os.environ.get('NEG') == 'nonmono':  # negative control: the old, live-only set
        Imono = set(incised)
    if Imono != set(incised):
        C['levels_with_extra'] += 1
        C['extra_edges'] += len(Imono - set(incised))
    if T.STATE.get('prevI') is not None and not T.STATE['prevI'] <= Imono:
        bad('not_monotone', level)
    cuts = [dict(v=ep['v'], ci=ep['ci'], mode=ep['mode'], e0=ep['e0']) for ep in epts]
    try:
        Gf = FGm.build_formal(emb, Imono, cuts)
        if Imono == set(incised):
            if FGm.edge_multiset(Gf) != FGm.code_multiset(Gc):
                bad('DEF_mismatch_with_code', level)
            else:
                C['DEF_match'] += 1
        T.check_level(emb, Gf, annuli, level)
        PREV['prev'] = extra_checks(emb, Gf, annuli, level, PREV.get('prev'))
    except Exception:
        bad('harness_exception', traceback.format_exc()[-600:])
    C['levels_checked'] += 1
    return Gc


thmD.build_ghat = wrapped


def main():
    rule, start, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if len(sys.argv) > 5:
        thmD.SIZE_MAX, thmD.GRID_MAX = int(sys.argv[4]), int(sys.argv[5])
    opts = dict(mode='claimed', variant='fixed', tiebreak='random', pairs=1, pcommon=0.3, pfar=0.5, e0rule=rule)
    nbad, t0 = 0, time.time()
    for sd in range(start, start + count):
        EVER.clear()
        I = thmD.make_instance(sd, None)
        chk, info = T.run_one(I, opts, sd * 7919 + 1)
        flags = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
        if flags:
            nbad += 1
            bad('THMD_FLAG', (sd, dict(flags)))
        C['instances'] += 1
    failing = {k: v for k, v in T.CNT.items()
               if k.startswith(('P1_', 'P2_', 'P3_rot', 'P3_dis', 'P3_euler_fail', 'P4_cop', 'P4_sig', 'P6_amb',
                                'P6_parent', 'FactN', 'closed', 'harness', 'DEF_mis', 'THMD'))}
    print(json.dumps(dict(rule=rule, start=start, count=count, thmD_bad=nbad, secs=round(time.time() - t0),
                          extra=dict(sorted(C.items())), check_level_failures=failing,
                          check_level_counts=dict(sorted(T.CNT.items())),
                          notes=NOTES + [str(x)[:300] for x in T.NOTES]), indent=1))


if __name__ == '__main__':
    main()
