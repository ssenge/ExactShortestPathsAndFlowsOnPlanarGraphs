"""Write thmD_O.py: the repository driver sim/thmD/thmD.py with checks for Lemma O.

Usage: python3 -I patchO.py SRC DST
The source file is read, never modified.
"""
import sys

src = open(sys.argv[1]).read()

# ---------------------------------------------------------------- 1. lambda_t with w = K c + 1
anchor1 = "    results = []   # dicts"
add1 = '''    KBIG = 10**9
    adjW1 = A1.adj(emb, KBIG)
    true_w = {}
    for tt in range(m + 1):
        dd = dijkstra(adjW1, {A1.piece[(tt, 0)]: 0})
        true_w[tt] = dd[A1.piece[(tt, 1)]]
'''
assert src.count(anchor1) == 1
src = src.replace(anchor1, add1 + anchor1, 1)

# ---------------------------------------------------------------- 2. checks at each incision
anchor2 = "            chain_l, chain_r = [], []\n"
add2 = '''            if opts.get('lemO'):
                lemma_O_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, X0, Y1, xt, yt, i1, i2,
                               ov, Pedges, m, true_w, KBIG, emb, stats, chk, lowhigh)
'''
assert src.count(anchor2) == 1
src = src.replace(anchor2, add2 + anchor2, 1)

# ---------------------------------------------------------------- 3. (INV) at child creation
anchor3 = "                nxt.append(C)\n"
add3 = '''                if opts.get('lemO'):
                    adjWC = C.adj(emb, KBIG)
                    for tt in range(jj, kk + 1):
                        if (tt, 0) not in C.piece or (tt, 1) not in C.piece:
                            chk.flag('O_INV_missing', (C.aid, tt, jj, kk))
                            continue
                        dd = dijkstra(adjWC, {C.piece[(tt, 0)]: 0})
                        stats['O_INV_checked'] += 1
                        if dd.get(C.piece[(tt, 1)]) != true_w[tt]:
                            chk.flag('O_INV_dist', (C.aid, tt, dd.get(C.piece[(tt, 1)]), true_w[tt]))
'''
assert src.count(anchor3) == 1
src = src.replace(anchor3, add3 + anchor3, 1)

# ---------------------------------------------------------------- 4. the check function
anchor4 = "def run_reif(emb, s, t, opts, rng, chk, info):"
add4 = r'''
def lemma_O_checks(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, X0, Y1, xt, yt, i1, i2,
                   ov, Pedges, m, true_w, KB, emb, stats, chk, lowhigh):
    """Checks of the claims of Lemma O (lemmaO.md) at one incision."""
    stats['O_incisions'] += 1
    Pa, Pb = A.left, A.right
    # (I5) strong form: d_A = lambda_t for every t with both pieces in A, in range or not
    adjI = A.adj(emb, KB)
    for tt in sorted(t_ for (t_, b_) in A.piece if b_ == 0 and (t_, 1) in A.piece):
        dd = dijkstra(adjI, {A.piece[(tt, 0)]: 0})
        stats['O_INVplus_%s' % ('in' if A.j <= tt <= A.k else 'out')] += 1
        if dd.get(A.piece[(tt, 1)]) != true_w[tt]:
            chk.flag('O_INVplus_dist', (A.aid, tt, dd.get(A.piece[(tt, 1)]), true_w[tt]))

    def ldset(ch):
        return set() if ch is None else {ld for e in ch['edges'] for ld in e}

    PaL, PbL = ldset(Pa), ldset(Pb)
    PaN = set() if Pa is None else set(Pa['nodes'])
    PbN = set() if Pb is None else set(Pb['nodes'])

    def lowend(X):
        return X.seq[0] if X.lowfirst else X.seq[-1]

    def highend(X):
        return X.seq[-1] if X.lowfirst else X.seq[0]

    def cut_at_low(X, ld):
        # the cut point of the old token ld is the low end of the arc of X
        return ((ld[1] == 2 and ld == X.seq[0] and X.lowfirst) or
                (ld[1] == 1 and ld == X.seq[-1] and not X.lowfirst))

    def cut_at_high(X, ld):
        return ((ld[1] == 2 and ld == X.seq[0] and not X.lowfirst) or
                (ld[1] == 1 and ld == X.seq[-1] and X.lowfirst))

    # ---- (I2): boundary paths, their end tokens, disjointness
    xa = ya = 0
    xb = yb = m
    for ch, nm in ((Pa, 'a'), (Pb, 'b')):
        if ch is None:
            continue
        s0, s1 = A.nodes[ch['nodes'][0]], A.nodes[ch['nodes'][-1]]
        if not (s0.anc[0] == 'p' and s0.anc[2] == 0 and s1.anc[0] == 'p' and s1.anc[2] == 1):
            chk.flag('O_I2_ends_kind', (A.aid, nm))
            continue
        for z in ch['nodes'][1:-1]:
            if A.nodes[z].anc[0] == 'p':
                chk.flag('O_I2_internal_P', (A.aid, nm))
        endf = cut_at_low if nm == 'a' else cut_at_high
        if not endf(s0, ch['edges'][0][0]):
            chk.flag('O_I2_first_tok', (A.aid, nm))
        if not endf(s1, ch['edges'][-1][1]):
            chk.flag('O_I2_last_tok', (A.aid, nm))
        if len(s0.seq) == 1 or len(s1.seq) == 1:
            stats['O_bound_end_single_token'] += 1
        if len(set(ch['nodes'])) != len(ch['nodes']):
            chk.flag('O_I2_not_simple', (A.aid, nm))
        if nm == 'a':
            xa, ya = s0.anc[1], s1.anc[1]
        else:
            xb, yb = s0.anc[1], s1.anc[1]
    if PaN & PbN:
        chk.flag('O_I2_PaPb_meet', A.aid)
    if Pa is not None and Pb is not None:
        stats['O_both_bounds'] += 1

    # ---- (I3): P-pieces exactly [xa, xb] and [ya, yb], range inside
    for bb, lo, hi in ((0, xa, xb), (1, ya, yb)):
        ts = sorted(t_ for (t_, b_) in A.piece if b_ == bb)
        if ts != list(range(lo, hi + 1)):
            chk.flag('O_I3_pieces', (A.aid, bb, lo, hi, ts))
    if not (xa <= A.j and ya <= A.j and A.k <= xb and A.k <= yb):
        chk.flag('O_I3_range', (A.aid, xa, ya, A.j, A.k, xb, yb))
    for X in A.nodes.values():
        if X.anc[0] == 'p' and not X.lowfirst in (True, False):
            chk.flag('O_lowfirst_missing', A.aid)

    # ---- (I4) old non-P tokens lie on Pa or Pb; at most one copy of each non-P edge
    copies = collections.defaultdict(set)
    for X in A.nodes.values():
        for ld in X.seq:
            e = ld[0] >> 1
            copies[e].add(frozenset((ld, partner(ld))))
            if ld[1] != 0 and e not in Pedges and ld not in PaL and ld not in PbL:
                chk.flag('O_I4_old_off_boundary', (A.aid, ld))
    for e, cs in copies.items():
        if e not in Pedges and len(cs) > 1:
            chk.flag('O_two_copies', (A.aid, e))

    # ---- Q as a path of A: internal nodes non-P, simple
    for z in Qn[1:-1]:
        if A.nodes[z].anc[0] == 'p':
            chk.flag('O_Q_internal_P', A.aid)
    if len(set(Qn)) != len(Qn):
        chk.flag('O_Q_not_simple', A.aid)
    if len(Qn) == 2:
        stats['O_Q_len1'] += 1
    if xt == yt:
        stats['O_x_eq_y'] += 1

    # ---- predicted sides
    ldpiece = {}
    for z, Z in newnodes.items():
        for ld in Z.seq:
            ldpiece[ld] = z
    pred = collections.defaultdict(set)

    def addp(z, lab, why):
        pred[z].add(lab)
        stats['O_pred_' + why] += 1

    Xparts = set(pieces.get(X0, [X0]))
    Yparts = set(pieces.get(Y1, [Y1]))
    for z, Z in newnodes.items():
        an = Z.anc
        if an[0] != 'p':
            continue
        if z in Xparts or z in Yparts:
            continue
        if (an[1], an[2]) in ((xt, 0), (yt, 1)):
            chk.flag('O3_second_piece_at_end', (A.aid, an))
            continue
        ref = xt if an[2] == 0 else yt
        addp(z, 'L' if an[1] < ref else 'R', 'P')

    zf, zl = Qe[0][0], Qe[-1][1]
    for Xid, tok, nm in ((X0, zf, 'x'), (Y1, zl, 'y')):
        X = A.nodes[Xid]
        if Xid in pieces:
            lo, hi = lowhigh(Xid)
            addp(lo, 'L', 'end_new')
            addp(hi, 'R', 'end_new')
        else:
            if tok[1] == 0:
                chk.flag('O_end_unsplit_new', (A.aid, nm))
            if len(X.seq) == 1:
                stats['O_end_old_single_token'] += 1
            if cut_at_low(X, tok):
                if tok not in PaL:
                    chk.flag('O_end_low_not_Pa', (A.aid, nm))
                addp(Xid, 'R', 'end_old_Pa')
            elif cut_at_high(X, tok):
                if tok not in PbL:
                    chk.flag('O_end_high_not_Pb', (A.aid, nm))
                addp(Xid, 'L', 'end_old_Pb')
            else:
                chk.flag('O_end_old_not_end', (A.aid, nm))
    Qlds = {ld for e in Qe for ld in e}
    for ld in PaL - Qlds:
        addp(ldpiece[ld], 'L', 'Pa_offQ')
    for ld in PbL - Qlds:
        addp(ldpiece[ld], 'R', 'Pb_offQ')
    for ld in Qlds & PaL:
        addp(ldpiece[ld], 'R', 'Q_old_on_Pa')
    for ld in Qlds & PbL:
        addp(ldpiece[ld], 'L', 'Q_old_on_Pb')
    for (la, lb) in Qe:
        if la[1] == 0:
            c1, c2 = ldpiece[(la[0], 1)], ldpiece[(la[0], 2)]
            if comp[c1] == comp[c2]:
                chk.flag('O_LP1_copies_same_comp', A.aid)
        elif la not in PaL and la not in PbL:
            chk.flag('O_Q_old_off_boundary', A.aid)
    # case (iv) nodes: S_in opposite to S_out (local parity), by components
    for k in range(1, len(Qn) - 1):
        x = Qn[k]
        X = A.nodes[x]
        if X.cyc:
            stats['O_node_cyclic'] += 1
            if len(pieces.get(x, [])) != 2:
                chk.flag('O_cyclic_not_two', A.aid)
            else:
                p, q = pieces[x]
                if comp[p] == comp[q]:
                    chk.flag('O_LP2_cyclic_same_comp', A.aid)
            continue
        stats['O_node_linear'] += 1
        onA, onB = x in PaN, x in PbN
        if not (onA or onB):
            chk.flag('O_linear_off_boundary', A.aid)
        u, w = Qe[k - 1][1], Qe[k][0]
        if x not in pieces:
            stats['O_node_iv_unchanged'] += 1
            continue
        parts = pieces[x]
        stats['O_node_iv_split%d' % len(parts)] += 1
        # S_in = the run from (the second half of) u to (the first half of) w, u before w in X
        ta, tb = Qe[k - 1][1], Qe[k][0]
        u_, w_ = (ta, tb) if X.seq.index(ta) < X.seq.index(tb) else (tb, ta)
        first = (u_[0], 2) if u_[1] == 0 else u_
        last = (w_[0], 1) if w_[1] == 0 else w_
        sin = ldpiece[first]
        if ldpiece[last] != sin:
            chk.flag('O_iv_sin_not_one_run', A.aid)
            continue
        sout = [p for p in parts if p != sin]
        for p in sout:
            if comp[p] == comp[sin]:
                chk.flag('O_LP2_iv_same_comp', A.aid)
        addp(sin, 'R' if onA else 'L', 'iv_Sin')

    # ---- (O1a, b): no component carries both labels
    lab_of_comp = collections.defaultdict(set)
    for z, labs in pred.items():
        lab_of_comp[comp[z]] |= labs
    for c_, labs in lab_of_comp.items():
        if len(labs) > 1:
            chk.flag('O1_mixed_component', (A.aid, xt, yt))
    for z, labs in pred.items():
        if len(labs) > 1:
            chk.flag('O1_mixed_piece', (A.aid, z))

    # ---- every component contains a part of a node of Q
    Qparts = set()
    for x in Qn:
        Qparts |= set(pieces.get(x, [x]))
    comps_with_Q = {comp[z] for z in Qparts}
    if set(comp.values()) - comps_with_Q:
        chk.flag('O_comp_without_Q', A.aid)

    # ---- (O2): sides without overlap
    PiE = {frozenset(e) for e in Pe_}
    bad = set()
    for ch in (Pa, Pb):
        if ch is None:
            continue
        inter = set(Pn_) & set(ch['nodes'])
        for (la, lb) in ch['edges']:
            if frozenset((la, lb)) in PiE:
                continue
            if A.ldmap[la] in inter or A.ldmap[lb] in inter:
                bad.add(la)
                bad.add(lb)
    for ld in bad:
        side = 'L' if ld in PaL else 'R'
        lab = lab_of_comp.get(comp[ldpiece[ld]], set())
        if lab and lab != {side}:
            chk.flag('O2_bad_edge_wrong_side', A.aid)
    for sd, sname in (('L', 'l'), ('R', 'r')):
        if ov.get((A.aid, sname)):
            stats['O2_overlap_side'] += 1
            ncomp = len({c_ for c_, labs in lab_of_comp.items() if labs == {sd}})
            if ncomp > 1:
                stats['O2_overlap_side_split'] += 1
            continue
        stats['O2_called_side'] += 1
        cs = {c_ for c_, labs in lab_of_comp.items() if labs == {sd}}
        if len(cs) != 1:
            chk.flag('O2_side_not_single', (A.aid, sd, len(cs)))
            continue
        C_ = cs.pop()
        for x in Qn:
            n_in = sum(1 for p in pieces.get(x, [x]) if comp[p] == C_)
            if n_in != 1:
                chk.flag('O2_node_parts', (A.aid, sd, n_in))
        for (la, lb) in Qe:
            if la[1] == 0:
                n_in = sum(1 for lab in (1, 2) if comp[ldpiece[(la[0], lab)]] == C_)
            else:
                n_in = 1 if comp[ldpiece[la]] == C_ else 0
            if n_in != 1:
                chk.flag('O2_edge_copies', (A.aid, sd, n_in))
        if any(comp[ldpiece[ld]] == C_ for ld in bad):
            chk.flag('O2_bad_in_called', (A.aid, sd))
        unl = [c_ for c_ in set(comp.values()) if c_ not in lab_of_comp]
        if unl:
            stats['O2_unlabelled_comp'] += 1

    # ---- (C23): every z in P_i and the bounding path, every m with both pieces in A
    adjW = None
    for sname, ch in (('l', Pa), ('r', Pb)):
        if ch is None:
            continue
        inter = sorted(set(Pn_) & set(ch['nodes']))
        if not inter:
            continue
        if adjW is None:
            adjW = A.adj(emb, KB)
        stats['O_c23_overlap'] += 1
        ms = sorted(t_ for (t_, b_) in A.piece if b_ == 0 and (t_, 1) in A.piece)
        dA = {}
        for mm in ms:
            dd = dijkstra(adjW, {A.piece[(mm, 0)]: 0})
            dA[mm] = dd[A.piece[(mm, 1)]]
            if dA[mm] != true_w[mm]:
                stats['O_lambda_differs_m_%s' % ('in' if A.j <= mm <= A.k else 'out')] += 1
        for zz in inter:
            stats['O_c23_z'] += 1
            dz = dijkstra(adjW, {zz: 0})
            for mm in ms:
                val = dz[A.piece[(mm, 0)]] + dz[A.piece[(mm, 1)]]
                if sname == 'l':
                    if A.j <= mm <= i:
                        cat = 'core'
                    elif i < mm <= i2:
                        cat = 'i_to_i2'
                    elif mm > i2:
                        cat = 'beyond_i2'
                    else:
                        cat = 'below_j'
                else:
                    if i <= mm <= A.k:
                        cat = 'core'
                    elif i1 <= mm < i:
                        cat = 'i_to_i2'
                    elif mm < i1:
                        cat = 'beyond_i2'
                    else:
                        cat = 'below_j'
                stats['O_c23_chk_' + cat] += 1
                if val != true_w[mm]:
                    stats['O_c23_neq_' + cat] += 1
                    if cat == 'core':
                        chk.flag('O_c23_core_fail', (A.aid, sname, mm, zz, val, true_w[mm]))
                if val != dA[mm]:
                    stats['O_c23_neqA_' + cat] += 1


'''
assert src.count(anchor4) == 1
src = src.replace(anchor4, add4 + anchor4, 1)

open(sys.argv[2], 'w').write(src)
print('ok')
