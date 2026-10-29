"""Referee additions to thmD_O.py (written by patchO.py).

1. Full-path reading of the bounding path: every chord also remembers the full P_i of the
   annulus that incised it. At each incision we look at common nodes z of P_i with the nodes of
   that full path that lie in A but are NOT on the incised copy (the bounding path of LEMMA_O),
   and test (C23) for them on [j_A, i] (j-side) or [i, k_A] (k-side).
2. Corner rule 'anycorner': any legal (corner, mode) pair of R0, uniformly.
3. Extra structural checks: single-token end pieces; [18]-literal discard (bad edges) on overlap
   sides.
Usage: python3 -I patchR.py thmD_O.py thmD_R.py
"""
import sys

src = open(sys.argv[1]).read()

a1 = "                chord = chord_of(None, cn, ce)\n"
assert src.count(a1) == 1
src = src.replace(a1, a1 + "                chord['full'] = list(Pn_)\n                chord['full_i'] = i\n", 1)

a2 = "        if opts.get('e0rule') == 'free':\n"
assert src.count(a2) == 1
add2 = '''        if opts.get('e0rule') == 'anycorner':
            dv = emb.deg(v)
            legal = [(i, 'L') for i in cs if (emb.rot[v][i] >> 1) not in Pedges]
            legal += [(i, 'R') for i in cs if (emb.rot[v][(i + 1) % dv] >> 1) not in Pedges]
            i, mo = rng.choice(legal)
            if mo == 'L':
                return dict(v=v, ci=i, mode='L', e0=emb.rot[v][i] >> 1)
            chk.flag('dev_mirrored_endpoint')
            return dict(v=v, ci=i, mode='R', e0=emb.rot[v][(i + 1) % dv] >> 1)
'''
src = src.replace(a2, add2 + a2, 1)

a3 = "                lemma_O_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, X0, Y1, xt, yt, i1, i2,\n"
assert src.count(a3) == 1
add3 = '''                referee_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, i1, i2, ov, true_w, KBIG,
                               emb, stats, chk)
'''
src = src.replace(a3, add3 + a3, 1)

a4 = "def lemma_O_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, X0, Y1, xt, yt, i1, i2,\n"
assert src.count(a4) == 1
add4 = r'''def referee_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, i1, i2, ov, true_w, KB, emb, stats, chk):
    Pset = set(Pn_)
    adjW = None
    for sname, ch in (('l', A.left), ('r', A.right)):
        if ch is None or 'full' not in ch:
            continue
        cop = set(ch['nodes'])
        fullin = {x for x in ch['full'] if x in A.nodes}
        extra = (Pset & fullin) - cop
        inc_ov = bool(Pset & cop)
        if not extra:
            continue
        stats['R_full_extra_side'] += 1
        if not inc_ov:
            stats['R_full_only_overlap'] += 1
        if adjW is None:
            adjW = A.adj(emb, KB)
        if sname == 'l':
            ms = range(A.j, i + 1)
            need = range(A.j, min(i1, A.k) + 1)
        else:
            ms = range(i, A.k + 1)
            need = range(max(i2, A.j), A.k + 1)
        for z in sorted(extra):
            dz = dijkstra(adjW, {z: 0})
            stats['R_full_z'] += 1
            bad_any = bad_need = False
            for mm in ms:
                if (mm, 0) not in A.piece or (mm, 1) not in A.piece:
                    continue
                val = dz[A.piece[(mm, 0)]] + dz[A.piece[(mm, 1)]]
                stats['R_full_chk'] += 1
                if val != true_w[mm]:
                    stats['R_full_neq'] += 1
                    bad_any = True
                    if mm in need:
                        bad_need = True
            if bad_any:
                stats['R_full_z_fail'] += 1
            if bad_need:
                stats['R_full_z_fail_need'] += 1
                if not inc_ov:
                    stats['R_full_z_fail_need_only_full'] += 1
                    # would the literal full-path reading lose the side's minimum?
                    best_true = min(true_w[mm] for mm in need)
                    best_rule = min(dz[A.piece[(mm, 0)]] + dz[A.piece[(mm, 1)]] for mm in ms)
                    if best_rule > best_true:
                        stats['R_full_loses_side_min'] += 1
    # single-token end pieces with an old end token (LEMMA_O sec. 11)
    for X_, tok in ((Qn[0], Qe[0][0]), (Qn[-1], Qe[-1][1])):
        if tok[1] != 0 and len(A.nodes[X_].seq) == 1:
            chk.flag('R_single_token_old_end', (A.aid, A.j, A.k))
    # [18]-literal discard on overlap sides: a component of the side without a bad edge
    PiE = {frozenset(e) for e in Pe_}
    for sname, ch in (('l', A.left), ('r', A.right)):
        if ch is None or not ov.get((A.aid, sname)):
            continue
        inter = Pset & set(ch['nodes'])
        badld = set()
        for (la, lb) in ch['edges']:
            if frozenset((la, lb)) in PiE:
                continue
            if A.ldmap[la] in inter or A.ldmap[lb] in inter:
                badld.add(la)
                badld.add(lb)
        if not badld:
            stats['R_overlap_side_no_bad_edge'] += 1


'''
src = src.replace(a4, add4 + a4, 1)
open(sys.argv[2], 'w').write(src)
print('ok')
