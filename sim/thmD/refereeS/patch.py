import sys
src = open(sys.argv[1]).read()
KB = "KBIG = 10**9\n"
# 1. after level-1 sanity, compute w-lengths in A1 with a large K
anchor1 = "    results = []   # dicts"
add1 = '''    KBIG = 10**9
    adjW1 = A1.adj(emb, KBIG)
    true_w = {}
    for tt in range(m + 1):
        dd = dijkstra(adjW1, {A1.piece[(tt, 0)]: 0})
        true_w[tt] = dd[A1.piece[(tt, 1)]]
    A1adj_nodes = {x: [y for (y, w) in adjW1[x]] for x in adjW1}
    def a1_sep(blocked, a, b):
        if a in blocked or b in blocked:
            return None
        seen = {a}; st = [a]
        while st:
            u = st.pop()
            if u == b:
                return False
            for v in A1adj_nodes[u]:
                if v not in seen and v not in blocked:
                    seen.add(v); st.append(v)
        return True
'''
assert anchor1 in src
src = src.replace(anchor1, add1 + anchor1, 1)
# 2. before chain_l: (O) full, S1 in w over all t, (S_1) at level 1, interval invariant
anchor2 = "            chain_l, chain_r = [], []\n"
add2 = '''            if opts.get('refS'):
                stats['R_incisions'] += 1
                # interval invariant of A's P-copies
                for bb in (0, 1):
                    ts = sorted(t_ for (t_, b_) in A.piece if b_ == bb)
                    if ts and ts != list(range(ts[0], ts[-1] + 1)):
                        chk.flag('R_copies_not_interval', (A.aid, bb, ts))
                if i1 < A.j or i2 > A.k:
                    stats['R_outside'] += 1
                # (O): no component holds both a left and a right P-piece
                sideof = {}
                for z, Z in newnodes.items():
                    an = Z.anc
                    if an[0] != 'p':
                        continue
                    if z in (X0, Y1):
                        continue
                    ref = xt if an[2] == 0 else yt
                    if an[1] < ref:
                        sideof[z] = 'L'
                    elif an[1] > ref:
                        sideof[z] = 'R'
                    else:
                        sideof[z] = None
                for (lo_, hi_) in ((lx, hx), (ly, hy)):
                    if lo_ is not None:
                        sideof[lo_] = 'L'
                        sideof[hi_] = 'R'
                if X0 not in pieces:
                    stats['R_unsplit_X'] += 1
                if Y1 not in pieces:
                    stats['R_unsplit_Y'] += 1
                compside = collections.defaultdict(set)
                for z, sd in sideof.items():
                    if sd is not None:
                        compside[comp[z]].add(sd)
                for c_, sds in compside.items():
                    if len(sds) > 1:
                        chk.flag('R_O_mixed_component', (A.aid, xt, yt))
                ncl = len({c_ for c_, s_ in compside.items() if s_ == {'L'}})
                ncr = len({c_ for c_, s_ in compside.items() if s_ == {'R'}})
                if ncl > 1 and not ov.get((A.aid, 'l')):
                    chk.flag('R_O_left_split_no_overlap', (A.aid,))
                if ncr > 1 and not ov.get((A.aid, 'r')):
                    chk.flag('R_O_right_split_no_overlap', (A.aid,))
                if ncl > 1 or ncr > 1:
                    stats['R_side_split'] += 1
                # (S) in A for every t strictly between x and y with both pieces in A (not only the range)
                for tt in range(min(xt, yt) + 1, max(xt, yt)):
                    z0, z1 = A.piece.get((tt, 0)), A.piece.get((tt, 1))
                    if z0 is None or z1 is None:
                        continue
                    stats['R_S_checked'] += 1
                    if comp.get(z0) == comp.get(z1):
                        chk.flag('R_S_fail_A', (A.aid, tt, xt, yt))
                # (S_1) at level 1, image of Q in A1, every t strictly between x and y
                Qimg = {amap.byanc[ctx.store[z].anc] for z in Qn}
                for tt in range(min(xt, yt) + 1, max(xt, yt)):
                    r_ = a1_sep(Qimg, A1.piece[(tt, 0)], A1.piece[(tt, 1)])
                    stats['R_S1_checked'] += 1
                    if r_ is None:
                        chk.flag('R_S1_on_Q', (A.aid, tt))
                    elif not r_:
                        chk.flag('R_S1_fail', (A.aid, tt, xt, yt))
                # Lemma S1 with w-lengths, every t in (i1, i2), in range or not
                for tt in range(i1 + 1, i2):
                    stats['R_S1w_checked'] += 1
                    if tt < A.j or tt > A.k:
                        stats['R_S1w_outside'] += 1
                    if not (all(true_w[q] <= true_w[tt] for q in range(i1, tt + 1)) or
                            all(true_w[q] <= true_w[tt] for q in range(tt, i2 + 1))):
                        chk.flag('R_S1w_fail', (A.aid, i1, i2, tt, A.j, A.k))
                # (a): w(P_i) = w(Q) + d(i,x) + d(i,y), and w(P_i) = true_w[i]
                wPi = sum(KBIG * emb.cap[la[0] >> 1] + 1 for la, lb in Pe_)
                if wPi != true_w[i]:
                    chk.flag('R_INV_i', (A.aid, i, wPi, true_w[i]))
'''
assert anchor2 in src
src = src.replace(anchor2, add2 + anchor2, 1)
# 3. at child creation: INV containment and distance for every t in range
anchor3 = "                nxt.append(C)\n"
add3 = '''                if opts.get('refS'):
                    adjWC = C.adj(emb, KBIG)
                    for tt in range(jj, kk + 1):
                        if (tt, 0) not in C.piece or (tt, 1) not in C.piece:
                            chk.flag('R_INV_missing', (C.aid, tt, jj, kk))
                            continue
                        dd = dijkstra(adjWC, {C.piece[(tt, 0)]: 0})
                        stats['R_INV_checked'] += 1
                        if dd.get(C.piece[(tt, 1)]) != true_w[tt]:
                            chk.flag('R_INV_dist', (C.aid, tt, dd.get(C.piece[(tt, 1)]), true_w[tt]))
'''
assert anchor3 in src
src = src.replace(anchor3, add3 + anchor3, 1)
# counters into summary
src = src.replace("'end_gt_trueA1', 'c24_checked', 'sep_checked'):",
  "'end_gt_trueA1', 'c24_checked', 'sep_checked', 'R_incisions', 'R_outside', 'R_unsplit_X', 'R_unsplit_Y', 'R_side_split', 'R_S_checked', 'R_S1_checked', 'R_S1w_checked', 'R_S1w_outside', 'R_INV_checked'):")
src = src.replace("                ends=a.ends)", "                ends=a.ends, refS=1)")
open(sys.argv[2], 'w').write(src)
print('ok')
