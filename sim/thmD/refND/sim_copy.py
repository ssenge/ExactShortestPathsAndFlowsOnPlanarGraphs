import os
"""Independent token-graph simulator, written from the paper's text only (not from thmD.py).
Pieces, pairs, I_l, recursion, bounds, overlap, ranges, repair; reading direction selectable."""
import heapq, random, collections
class Inst:
    def __init__(s, n, ends, rot, cap, S, T):
        s.n, s.ends, s.rot, s.cap, s.s, s.t = n, [tuple(e) for e in ends], rot, cap, S, T
        s.m = len(ends)
        s.pos = {d: (v, k) for v, r in enumerate(rot) for k, d in enumerate(r)}
        for d, (v, k) in s.pos.items():
            assert s.ends[d >> 1][d & 1] == v, 'dart 2e leaves first end'
        s.faces, s.face_of = [], {}
        for d0 in range(2 * s.m):
            if d0 in s.face_of: continue
            f, d = [], d0
            while d not in s.face_of:
                s.face_of[d] = len(s.faces); f.append(d); d = s.fnext(d)
            s.faces.append(f)
    def fnext(s, d):
        v, k = s.pos[d ^ 1]; r = s.rot[v]; return r[(k + 1) % len(r)]
    def euler(s): return s.n - s.m + len(s.faces)
    def corner_face(s, v, k):
        r = s.rot[v]; return s.face_of[r[(k + 1) % len(r)]]
    def corner_darts(s, v, k):
        r = s.rot[v]; return r[k] ^ 1, r[(k + 1) % len(r)]   # incoming dart, outgoing dart in the walk

def token_graph(I, inc, cornercuts):
    """returns piece_of[token], pieces[pid]=[tokens], cyclic[pid], partner[token]."""
    cut_after = set(cornercuts)  # (in dart, out dart)
    piece_of, pieces, cyclic = {}, [], []
    for f in I.faces:
        toks = []
        for d in f:
            toks += [(d, 1), (d, 2)] if d >> 1 in inc else [(d, 0)]
        L = len(toks)
        def cut(a, b):
            if a[0] == b[0] and a[1] == 1 and b[1] == 2: return True
            return a[0] != b[0] and (a[0], b[0]) in cut_after or (a[0] == b[0] and L == 1 and (a[0], b[0]) in cut_after)
        cuts = [q for q in range(L) if cut(toks[q], toks[(q + 1) % L])]
        if not cuts:
            pid = len(pieces); pieces.append(list(toks)); cyclic.append(True)
            for x in toks: piece_of[x] = pid
            continue
        st = (cuts[0] + 1) % L
        rot_t = toks[st:] + toks[:st]
        cur = []
        for q, x in enumerate(rot_t):
            cur.append(x)
            if cut(x, rot_t[(q + 1) % L]):
                pid = len(pieces); pieces.append(cur); cyclic.append(False)
                for y in cur: piece_of[y] = pid
                cur = []
        assert not cur
    partner = {}
    for e in range(I.m):
        d, r = 2 * e, 2 * e + 1
        if e in inc:
            partner[(d, 1)] = (r, 2); partner[(r, 2)] = (d, 1)
            partner[(d, 2)] = (r, 1); partner[(r, 1)] = (d, 2)
        else:
            partner[(d, 0)] = (r, 0); partner[(r, 0)] = (d, 0)
    return piece_of, pieces, cyclic, partner

class Fail(Exception): pass

def dijk(pieces, partner, piece_of, src, length):
    dist = {src: 0}; par = {src: None}; cnt = {src: 1}; pq = [(0, src)]; done = set()
    while pq:
        dd, u = heapq.heappop(pq)
        if u in done: continue
        done.add(u)
        for x in pieces[u]:
            y = partner[x]; v = piece_of[y]; nd = dd + length(x[0] >> 1)
            if v not in dist or nd < dist[v]:
                dist[v] = nd; par[v] = (u, x, y); cnt[v] = cnt[u]; heapq.heappush(pq, (nd, v))
            elif nd == dist[v] and v not in done and u != v:
                cnt[v] += cnt[u]
    return dist, par, cnt

def path(par, tgt):
    nodes, es = [tgt], []
    while par[nodes[0]] is not None:
        u, x, y = par[nodes[0]]; es.insert(0, (x, y)); nodes.insert(0, u)
    return nodes, es

def run(I, f, g, corner_s, corner_t, length=None, repair=False, reading='0', rng=None, log=None, stats=None, flip=False):
    """corner_* = rotation index. reading: '0' read from g_i^0 ; 'random': per annulus."""
    stats = stats if stats is not None else collections.Counter()
    length = length or (lambda e: I.cap[e])
    def L(*a):
        if log is not None: log.append(' '.join(map(str, a)))
    # level 0: P
    pof0, pc0, _, pt0 = token_graph(I, set(), [])
    dist, par, cnt = dijk(pc0, pt0, pof0, pof0[(I.faces[f][0], 0)], length)
    nodes, es = path(par, pof0[(I.faces[g][0], 0)])
    Pf = [pof0[(I.faces[0][0], 0)]] and [I.face_of[pc0[x][0][0]] for x in nodes]
    Pe = [x[0] >> 1 for x, y in es]
    Pdart = [x[0] for x, y in es]  # dart in p_{k}, for the edge between p_k, p_{k+1}
    m = len(Pf) - 1
    stats['P_nonunique'] += cnt[pof0[(I.faces[g][0], 0)]] != 1
    assert I.corner_face(I.s, corner_s) == f and I.corner_face(I.t, corner_t) == g
    cc = [I.corner_darts(I.s, corner_s), I.corner_darts(I.t, corner_t)]
    Inc = set(Pe)
    # anc: level-1 token -> (t, sigma) via forward/reverse run
    pof, pcs, cyc, pt = token_graph(I, Inc, cc)
    anc_tok = {}
    for t, h in enumerate(Pf):
        ps = sorted({pof[x] for d in I.faces[h] for x in ([(d, 1), (d, 2)] if d >> 1 in Inc else [(d, 0)])})
        if len(ps) != 2: raise Fail('face of P not two pieces: %s' % ps)
        for p in ps:
            first = pcs[p][0]; last = pcs[p][-1]
            entry_ok = (first == (Pdart[t - 1] ^ 1, 2)) if t > 0 else (first[0] == cc[0][1] and first[1] != 2)
            sig = 0 if entry_ok else 1
            if flip: sig = 1 - sig
            for x in pcs[p]: anc_tok[x] = (t, sig)
    def anc(x):   # token of any level -> (t, sigma) or None
        d, l = x
        if d >> 1 in Pe: return anc_tok.get(x)
        return anc_tok.get((d, 0))
    lam = {}
    for t in range(m + 1):
        a = [p for p in {pof[x] for x in anc_tok} if anc(pcs[p][0]) == (t, 0)][0]
        b = [p for p in {pof[x] for x in anc_tok} if anc(pcs[p][0]) == (t, 1)][0]
        lam[t] = dijk(pcs, pt, pof, a, length)[0][b]
    results = []
    live = [dict(root=pcs[0][0], j=0, k=m, Pa=[], Pb=[])]
    level = 1
    while live:
        pof, pcs, cyc, pt = token_graph(I, Inc, cc)
        newinc = set(); nxt = []
        for A in live:
            # component of root
            seen = {pof[A['root']]}; st = [pof[A['root']]]
            while st:
                u = st.pop()
                for x in pcs[u]:
                    v = pof[pt[x]]
                    if v not in seen: seen.add(v); st.append(v)
            G = {}
            for u in seen:
                a = anc(pcs[u][0])
                if a is not None:
                    if a in G: raise Fail('(Pieces) two pieces of %s' % (a,))
                    G[a] = u
            j, k = A['j'], A['k']
            def sssp(src): return dijk(pcs, pt, pof, src, length)
            def compute(t, tag):
                src = G[(t, 0)]
                d, pr, cn = sssp(src)
                tgt = G[(t, 1)]
                if d[tgt] != lam[t]: raise Fail('(Dist) t=%d %s %s' % (t, d[tgt], lam[t]))
                results.append((t, d[tgt], tag, level))
                stats['nonunique'] += cn[tgt] != 1
                if cn[tgt] != 1: L('   tie at t=%d tag=%s level=%d len=%d count=%d' % (t, tag, level, d[tgt], cn[tgt]))
                return d, pr, tgt
            if k <= j + 1:
                compute(j, 'leaf'); 
                if k != j: compute(k, 'leaf')
                L('L%d leaf [%d,%d]' % (level, j, k))
                continue
            i = (j + k) // 2
            d, pr, tgt = compute(i, 'Pi')
            nodes, es = path(pr, tgt)
            lab = [anc(pcs[u][0]) for u in nodes]
            ps = [a for a in lab if a]
            sg = [a[1] for a in ps]
            stats['alternations>1'] += sum(sg[q] != sg[q + 1] for q in range(len(sg) - 1)) > 1
            stats['Pi'] += 1
            i1, i2 = min(a[0] for a in ps), max(a[0] for a in ps)
            rd0 = reading == '0' or (reading == 'random' and rng.random() < .5)
            if rd0:
                q0 = max(q for q, a in enumerate(lab) if a and a[1] == 0)
                q1 = min(q for q, a in enumerate(lab) if q > q0 and a and a[1] == 1)
            else:
                q1 = min(q for q, a in enumerate(lab) if a and a[1] == 1)
                q0 = max(q for q, a in enumerate(lab) if q < q1 and a and a[1] == 0)
            Qn, Qe = nodes[q0:q1 + 1], es[q0:q1]
            x, y = lab[q0][0], lab[q1][0]
            for u in Qn[1:-1]:
                if anc(pcs[u][0]) is not None: raise Fail('P-piece inside Q')
            stats['hull_ok'] += (i1, i2) == (min(i, x, y), max(i, x, y))
            stats['hull_bad'] += (i1, i2) != (min(i, x, y), max(i, x, y))
            if repair:
                im, ip = max(i1, j), min(i2, k)
                for t in {im, ip} - {i}: compute(t, 'end')
            nodesA = lambda bound: {pof[tk] for pr_ in bound for tk in pr_}
            ova, ovb = bool(nodesA(A['Pa']) & set(nodes)), bool(nodesA(A['Pb']) & set(nodes))
            # local test (Pieces): nodes of the bounds = nodes with an old token of an edge off P
            oldoff = {u for u in seen if any(tk[1] and (tk[0] >> 1) not in Pe for tk in pcs[u])}
            if oldoff != nodesA(A['Pa']) | nodesA(A['Pb']): raise Fail('(Pieces) local test')
            L('L%d A[%d,%d] P_%d=%s len=%d x=%d y=%d i1=%d i2=%d ova=%s ovb=%s edges=%s' % (level, j, k, i, ' '.join('p%d^%d' % a if a else 'f%d' % I.face_of[pcs[u][0][0]] for a, u in zip(lab, nodes)), d[tgt], x, y, i1, i2, ova, ovb, [xx[0] >> 1 for xx, yy in es]))
            if ova:
                stats['overlap_a'] += 1
                dz, _, _ = sssp(sorted(nodesA(A['Pa']) & set(nodes))[0])
                for t in range(j, i + 1): 
                    v = dz[G[(t, 0)]] + dz[G[(t, 1)]]
                    if v != lam[t]: raise Fail('(C23) a')
                    results.append((t, v, 'ov', level))
            if ovb:
                stats['overlap_b'] += 1
                dz, _, _ = sssp(sorted(nodesA(A['Pb']) & set(nodes))[0])
                for t in range(i, k + 1):
                    v = dz[G[(t, 0)]] + dz[G[(t, 1)]]
                    if v != lam[t]: raise Fail('(C23) b')
                    results.append((t, v, 'ov', level))
            # sides: F1 rule. high pair {(d,2),(rev d,1)}, d the dart at the earlier node along Q (0->1), 0=forward
            hi, lo = [], []
            for a, b in Qe:
                e = a[0] >> 1
                if a[1] == 0:
                    dd = a[0]
                    if flip: H, Lw = frozenset([(dd, 1), (dd ^ 1, 2)]), frozenset([(dd, 2), (dd ^ 1, 1)])
                    else: H, Lw = frozenset([(dd, 2), (dd ^ 1, 1)]), frozenset([(dd, 1), (dd ^ 1, 2)])
                    hi.append(H); lo.append(Lw); newinc.add(e)
                else:
                    hi.append(frozenset([a, b])); lo.append(frozenset([a, b]))
            A['_q'] = dict(hi=hi, lo=lo, i1=i1, i2=i2, x=x, y=y, ova=ova, ovb=ovb, seen=seen, G=dict(G), Qn=Qn, Qe=Qe)
            if not ova and j <= i1:
                nxt.append(dict(root=sorted(lo[0])[0], j=j, k=i1, Pa=A['Pa'], Pb=lo, side='lo', par=A))
            if not ovb and i2 <= k:
                nxt.append(dict(root=sorted(hi[0])[0], j=i2, k=k, Pa=hi, Pb=A['Pb'], side='hi', par=A))
        Inc = Inc | newinc
        # check the side rule and one-sidedness on the next level
        pof2, pcs2, cyc2, pt2 = token_graph(I, Inc, cc)
        def comp2(root):
            seen = {pof2[root]}; st = [pof2[root]]
            while st:
                u = st.pop()
                for x in pcs2[u]:
                    v = pof2[pt2[x]]
                    if v not in seen: seen.add(v); st.append(v)
            return seen
        for c in nxt:
            q = c['par']['_q']; S = comp2(c['root'])
            _idx = [anc(pcs2[u][0]) for u in S if anc(pcs2[u][0]) is not None]
            _other = [a for a in _idx if a[0] != (q['x'] if a[1] == 0 else q['y'])]
            stats['child_only_end_parts'] += not _other
            stats['child_only_end_parts_x_eq_y'] += (not _other) and q['x'] == q['y']
            stats['child_range_outside_own_piece_index'] += 0
            for u in S:
                a = anc(pcs2[u][0])
                if a is None: continue
                t, sg = a; pivot = q['x'] if sg == 0 else q['y']
                if t != pivot:
                    want = 'hi' if t > pivot else 'lo'
                    stats['side_checks'] += 1
                    if want != c['side']: raise Fail('side rule (P-piece) %s %s' % (a, c['side']))
            other = q['lo'] if c['side'] == 'hi' else q['hi']
            mine = q['hi'] if c['side'] == 'hi' else q['lo']
            for pr_ in other:
                if pr_ in mine: continue   # old edge of Q: one pair
                for tk in pr_:
                    if pof2[tk] in S: raise Fail('(O b) called side holds two pairs')
            for pr_ in mine:
                for tk in pr_:
                    if pof2[tk] not in S: raise Fail('(O b) copy of Q not in the side')
            stats['called'] += 1
        live = nxt; level += 1
    return dict(results=results, lam=lam, Pf=Pf, Pe=Pe, m=m)
