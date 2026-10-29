"""Exhaustive level-1 attack on Lemma R / Lemma N.

For every map (emb.enumerate_maps), capacity assignment, s != t, f in s*, g in t*, shortest
simple dual path P (ties enumerated up to a cap), every corner of s in p_0 and of t in p_m and
every legal mode:
  * (5) a legal choice exists; every corner of s in p_0 has a flank off P
  * R2: P-faces split in exactly two pieces, other faces one cyclic piece; no empty piece
  * Lemma N level 1: G*_1 connected
  * abstract [18] incision along gamma (abstract18.Model) equals pieces + pairs of R1/R2
  * Reif reduction: min_k d_1(p_k^0, p_k^1) = lambda (lambda by brute force over vertex sets)
  * Def R properties (1), (2), (4), Claim 1, and (3): Table R consistent and Euler
  * Theorem D distance bullet on G^_1: dist = d_K between the copies of p_k^0 and p_k^1
usage: python3 -I level1.py NMAX MMAX NCAPS WORKERS [PMAX]
"""
import sys, os, collections, itertools, random, heapq, json, time, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emb import Emb, enumerate_maps
import defr
from abstract18 import Model

INF = float('inf')


def mincut_brute(emb, s, t):
    others = [v for v in range(emb.n) if v not in (s, t)]
    best = INF
    for k in range(1 << len(others)):
        S = {s} | {others[j] for j in range(len(others)) if k >> j & 1}
        val = sum(emb.cap[e] for e, (u, v) in enumerate(emb.ends) if (u in S) != (v in S))
        best = min(best, val)
    return best


def dual_adj(emb):
    A = collections.defaultdict(list)
    for e in range(emb.m):
        f, g = emb.face_of[2 * e], emb.face_of[2 * e + 1]
        if f != g:
            A[f].append((g, e))
            A[g].append((f, e))
    return A


def dijkstra(A, src, w):
    dist = {src: 0}
    pq = [(0, src)]
    done = set()
    while pq:
        d, x = heapq.heappop(pq)
        if x in done:
            continue
        done.add(x)
        for y, e in A[x]:
            nd = d + w(e)
            if nd < dist.get(y, INF):
                dist[y] = nd
                heapq.heappush(pq, (nd, y))
    return dist


def shortest_paths(emb, A, f, g, cap, rng):
    """simple shortest f-g dual paths (faces, edges), up to cap, random order."""
    w = lambda e: emb.cap[e]
    df = dijkstra(A, f, w)
    dg = dijkstra(A, g, w)
    D = df[g]
    out = []
    seen = set()
    # randomized DFS on tight edges: df[x] + c + dg[y] == D
    for attempt in range(cap * 4):
        if len(out) >= cap:
            break
        path_f, path_e = [f], []
        vis = {f}
        ok = True
        cur = f
        while cur != g:
            cand = [(y, e) for (y, e) in A[cur]
                    if y not in vis and df[cur] + w(e) + dg[y] == D]
            if not cand:
                ok = False
                break
            y, e = rng.choice(cand)
            path_f.append(y)
            path_e.append(e)
            vis.add(y)
            cur = y
        if ok:
            key = tuple(path_e) + (f, g)
            if key not in seen:
                seen.add(key)
                out.append((path_f, path_e))
    return out, D


def legal(emb, z, face, Pedges):
    """legal (corner index, mode) at terminal z with corner in face."""
    res = []
    corners = []
    for i in range(emb.deg(z)):
        c = (z, i)
        if emb.corner_face(c) != face:
            continue
        corners.append(i)
        A = emb.r(z, i) >> 1
        B = emb.r(z, i + 1) >> 1
        if A not in Pedges:
            res.append((i, 'L'))
        if B not in Pedges:
            res.append((i, 'R'))
    return corners, res


def piece_dist(G, emb, srcs, w):
    """Dijkstra on G*_l (pieces, pairs) from a set of pieces."""
    A = collections.defaultdict(list)
    for (x, y) in G.pairs:
        a, b = G.piece_of[x], G.piece_of[y]
        c = w(x[0] >> 1)
        A[a].append((b, c))
        A[b].append((a, c))
    dist = {s: 0 for s in srcs}
    pq = [(0, s) for s in srcs]
    done = set()
    while pq:
        d, x = heapq.heappop(pq)
        if x in done:
            continue
        done.add(x)
        for y, c in A[x]:
            if d + c < dist.get(y, INF):
                dist[y] = d + c
                heapq.heappush(pq, (d + c, y))
    return dist


def ghat_dist(G, emb, src_keys, K, M):
    adj = collections.defaultdict(list)
    for (a, b, t, info) in G.E:
        if t == 'R':
            w = 0
        elif t == 'S':
            w = M
        else:
            w = K * emb.cap[info[0][0] >> 1] + 1
        adj[a].append((b, w))
        adj[b].append((a, w))
    dist = {k: 0 for k in src_keys}
    pq = [(0, k) for k in src_keys]
    done = set()
    while pq:
        d, x = heapq.heappop(pq)
        if x in done:
            continue
        done.add(x)
        for y, w in adj[x]:
            if d + w < dist.get(y, INF):
                dist[y] = d + w
                heapq.heappush(pq, (d + w, y))
    return dist


def compare_abstract(G, emb, M, bad):
    """abstract node-parts and dual edges vs pieces and pairs (whole G*_1)."""
    piece_key = {}
    for pi, P in enumerate(G.pieces):
        T = tuple(P['toks'])
        if P['cyclic']:
            k = min(range(len(T)), key=lambda j: T[j:] + T[:j])
            T = T[k:] + T[:k]
        piece_key[(P['face'], T, P['cyclic'])] = pi
    if len(piece_key) != len(G.pieces):
        bad('abs_piece_key_collision', None)
    node2piece = {}
    for nid, X in M.np.items():
        T, ns = M.tokens_of(nid)
        if ns > 1:
            bad('abs_multi_seam', (nid, X.items))
        T = tuple(T)
        cyc = ns == 0
        if cyc:
            k = min(range(len(T)), key=lambda j: T[j:] + T[:j])
            T = T[k:] + T[:k]
        pi = piece_key.get((X.face, T, cyc))
        if pi is None:
            bad('abs_node_not_a_piece', (X.face, T, cyc))
            continue
        node2piece[nid] = pi
    if len(set(node2piece.values())) != len(G.pieces) or len(node2piece) != len(M.np):
        bad('abs_piece_count', (len(node2piece), len(M.np), len(G.pieces)))
    lab = {'all': 0, 'tail': 1, 'head': 2}
    abs_pairs = set()
    for h in M.he.values():
        if h.node is None or h.node not in M.np:
            continue
        p = M.he[h.partner]
        abs_pairs.add(frozenset([(h.dart, lab[h.kind]), (p.dart, lab[p.kind])]))
    r1 = {frozenset(p) for p in G.pairs}
    if abs_pairs != r1:
        bad('abs_pairs_differ', (sorted(map(sorted, abs_pairs - r1))[:3], sorted(map(sorted, r1 - abs_pairs))[:3]))
    return node2piece


def run_instance(emb, s, t, pf, pe, lam, C, bad, rng, opts):
    m = len(pf) - 1
    Pedges = set(pe[1:]) if False else set(pe)
    corners_s, legal_s = legal(emb, s, pf[0], Pedges)
    corners_t, legal_t = legal(emb, t, pf[m], Pedges)
    C['P_paths'] += 1
    # (5)
    if not corners_s or not corners_t:
        bad('P5_no_corner', (s, t, pf))
        return
    for z, cs_, lg in ((s, corners_s, legal_s), (t, corners_t, legal_t)):
        for i in cs_:
            if not any(j == i for j, _ in lg):
                bad('P5_corner_without_flank', (z, i, pf, pe))
    if not legal_s or not legal_t:
        bad('P5_no_legal', None)
        return
    if len(corners_s) > 1:
        C['cov_several_corners_s'] += 1
    if m == 0:
        C['cov_m0'] += 1
    for (z, cl) in ((s, corners_s), (t, corners_t)):
        if emb.deg(z) == 1:
            C['cov_deg1_terminal'] += 1
    by_corner_s = collections.defaultdict(list)
    for i, mu in legal_s:
        by_corner_s[i].append(mu)
    by_corner_t = collections.defaultdict(list)
    for i, mu in legal_t:
        by_corner_t[i].append(mu)
    I = set(pe)
    K = None
    for cs in sorted(by_corner_s):
        for ct in sorted(by_corner_t):
            C['corner_pairs'] += 1
            cuts0 = [dict(z=s, i=cs, mode=by_corner_s[cs][0], role='s'),
                     dict(z=t, i=ct, mode=by_corner_t[ct][0], role='t')]
            if 'd3_literal' in opts.get('var', ()):
                # [18] Remark 3.3 read literally: e0 = e_i always uses corner i (copy v_i^L)
                for cu in cuts0:
                    if cu['mode'] == 'R':
                        cu['i'] = (cu['i'] + 1) % emb.deg(cu['z'])
                        cu['mode'] = 'L'
                if cuts0[0]['z'] == cuts0[1]['z'] and cuts0[0]['i'] == cuts0[1]['i']:
                    continue
            G0 = defr.build(emb, I, cuts0, opts.get("var", frozenset()))
            # R2 structure
            byface = collections.Counter(P['face'] for P in G0.pieces)
            for f in range(len(emb.faces)):
                want = 2 if f in pf else 1
                if byface[f] != want:
                    bad('R2_piece_count', (f, byface[f], want))
            # Lemma N level 1: connected
            comp = defr.token_components(G0)
            if len(set(comp)) != 1:
                bad('N_level1_disconnected', (s, t, pf, pe, cs, ct))
            C['N_level1_checked'] += 1
            # abstract [18] incision along gamma
            M = Model(emb)
            try:
                side = M.incise_gamma(pf, {k + 1: pe[k] for k in range(m)}, (s, cs), (t, ct))
                n2p = compare_abstract(G0, emb, M, bad)
                if M.flags:
                    for k, v in M.flags.items():
                        bad('abs_flag_' + k, M.notes[:2])
                C['abs_level1_compared'] += 1
            except Exception:
                bad('abs_exception', traceback.format_exc()[-500:])
                n2p = None
            # reduction
            w = lambda e: emb.cap[e]
            best = INF
            pk = {}
            for k in range(m + 1):
                ps = [pi for pi, P in enumerate(G0.pieces) if P['face'] == pf[k]]
                if len(ps) != 2:
                    continue
                pk[k] = ps
                d = piece_dist(G0, emb, [ps[0]], w)
                best = min(best, d.get(ps[1], INF))
            C['reduction_checked'] += 1
            if best != lam:
                bad('reduction', dict(s=s, t=t, pf=pf, pe=pe, cs=cs, ct=ct, got=best, lam=lam))
            # abstract sides agree with piece pairs: (k,0),(k,1) map to the two pieces of p_k
            if n2p is not None:
                for k in range(m + 1):
                    a, b = side.get((k, 0)), side.get((k, 1))
                    if a is None or b is None or {n2p.get(a), n2p.get(b)} != set(pk.get(k, [])):
                        bad('abs_sides', k)
            # Def R per legal mode pair
            for ms in by_corner_s[cs]:
                for mt in by_corner_t[ct]:
                    cuts = [dict(z=s, i=cs, mode=ms, role='s'), dict(z=t, i=ct, mode=mt, role='t')]
                    G = defr.build(emb, I, cuts, opts.get('var', frozenset()))
                    C['defR_built'] += 1
                    C['mode_' + ms + mt] += 1
                    if G.e0 == G.elast:
                        C['cov_e0_eq_elast'] += 1
                    e0 = G.e0
                    if emb.face_of[2 * e0] == pf[0] and emb.face_of[2 * e0 + 1] == pf[0]:
                        C['cov_e0_both_darts_p0'] += 1
                    defr.check_props(G, bad)
                    ok = defr.check_planar(G, bad, use_nx=opts.get('nx', False))
                    C['P3_checked'] += 1
                    for c in G.cutc:
                        x, _ = G.moved[c]
                        eid, end = G.ECof[x]
                        if G.E[eid][end] == ('X',) + c:
                            C['cov_X_deg3'] += 1
                    if any(a == b for (a, b, tt, info) in G.E if tt == 'C'):
                        C['cov_EC_selfloop'] += 1
                    # distance bullet of Theorem D on G^_1
                    if opts.get('dist', True):
                        if K is None:
                            K = len(G.V) + 1 + 4
                        Mw = K * (2 * sum(emb.cap) + 1) + 1
                        wK = lambda e: K * emb.cap[e] + 1
                        for k, ps in pk.items():
                            dK = piece_dist(G, emb, [ps[0]], wK).get(ps[1], INF)
                            src = [kk for kk, pi in G.vpiece.items() if pi == ps[0]]
                            dst = [kk for kk, pi in G.vpiece.items() if pi == ps[1]]
                            dd = ghat_dist(G, emb, src[:1], K, Mw)
                            got = {dd.get(y, INF) for y in dst}
                            if got != {dK}:
                                bad('thmD_distance', (k, got, dK))
                        C['dist_checked'] += 1


def capsets(m, rng, ncaps):
    out = [[1] * m]
    for j in range(ncaps - 1):
        if j % 2 == 0:
            out.append([rng.choice([0, 1, 1, 2, 3]) for _ in range(m)])
        else:
            out.append([rng.choice([1, 2, 3, 4, 7]) for _ in range(m)])
    return out


def work(args):
    maps, ncaps, pmax, seed, opts = args
    C = collections.Counter()
    notes = []

    def mkbad(ctx):
        def bad(k, v):
            C['BAD_' + k] += 1
            if len(notes) < 40:
                notes.append((k, str(v)[:600], ctx[0]))
        return bad
    rng = random.Random(seed)
    for (n, ends, rot) in maps:
        base = Emb(n, ends, rot)
        if any(base.face_of[2 * e] == base.face_of[2 * e + 1] for e in range(base.m)):
            C['cov_maps_with_bridge'] += 1
        if any(len(f) == 2 for f in base.faces):
            C['cov_maps_with_2gon'] += 1
        for cap in capsets(base.m, rng, ncaps):
            emb = base.with_cap(cap)
            A = dual_adj(emb)
            for s in range(n):
                for t in range(n):
                    if s == t:
                        continue
                    lam = mincut_brute(emb, s, t)
                    sf = sorted({emb.corner_face((s, i)) for i in range(emb.deg(s))})
                    tf = sorted({emb.corner_face((t, i)) for i in range(emb.deg(t))})
                    if set(sf) & set(tf):
                        C['cov_st_common_face'] += 1
                    for f in sf:
                        for g in tf:
                            paths, D = shortest_paths(emb, A, f, g, pmax, rng)
                            for pf, pe in paths:
                                ctx = [dict(n=n, ends=ends, rot=rot, cap=cap, s=s, t=t, pf=pf, pe=pe)]
                                try:
                                    run_instance(emb, s, t, pf, pe, lam, C, mkbad(ctx), rng, opts)
                                except Exception:
                                    C['BAD_exception'] += 1
                                    if len(notes) < 40:
                                        notes.append(('exception', traceback.format_exc()[-800:], ctx[0]))
        C['maps'] += 1
    return C, notes


def main():
    nmax, mmax, ncaps, workers = map(int, sys.argv[1:5])
    pmax = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    var = frozenset(sys.argv[6].split(',')) if len(sys.argv) > 6 and sys.argv[6] else frozenset()
    opts = dict(var=var, dist=True)
    t0 = time.time()
    L = enumerate_maps(nmax, mmax)
    allmaps = [M for m in sorted(L) for M in L[m]]
    chunks = [allmaps[i::workers * 4] for i in range(workers * 4)]
    import multiprocessing as mp
    C = collections.Counter()
    notes = []
    with mp.Pool(workers) as pool:
        for c, nt in pool.imap_unordered(work, [(ch, ncaps, pmax, 1000 + j, opts) for j, ch in enumerate(chunks)]):
            C.update(c)
            notes += nt
    out = dict(args=sys.argv[1:], secs=round(time.time() - t0), maps=len(allmaps),
               counts=dict(sorted(C.items())), notes=notes[:60])
    print(json.dumps(out, indent=1, default=str))


if __name__ == '__main__':
    main()
