"""Numerical attack on Lemma D (weighted face-disjoint graph) and Theorems C / C'.

Conventions: F(d) = face containing half-edge d in networkx traversal.
Dual dart of d goes F(d) -> F(rev d), length lam(d).
Flow from potentials: f(d) = phi(F(rev d)) - phi(F(d)) (+ f0(d)).
"""
import random, itertools, sys
import networkx as nx

INF = float('inf')


def bellman_ford(nodes, arcs, src):
    """arcs: list of (a,b,w). returns dist dict or None if negative cycle reachable from src."""
    dist = {x: INF for x in nodes}
    dist[src] = 0
    n = len(nodes)
    for it in range(n):
        ch = False
        for a, b, w in arcs:
            if dist[a] < INF and dist[a] + w < dist[b]:
                dist[b] = dist[a] + w
                ch = True
        if not ch:
            return dist
    return None


def has_neg_cycle(nodes, arcs):
    # virtual source to all
    vs = ('VS',)
    arcs2 = arcs + [(vs, x, 0) for x in nodes]
    return bellman_ford(list(nodes) + [vs], arcs2, vs) is None


def random_planar(rows, cols, p_keep, rng):
    G = nx.grid_2d_graph(rows, cols)
    for r in range(rows - 1):
        for c in range(cols - 1):
            if rng.random() < 0.5:
                G.add_edge((r, c), (r + 1, c + 1))
            else:
                G.add_edge((r + 1, c), (r, c + 1))
    edges = list(G.edges())
    rng.shuffle(edges)
    for e in edges:
        if rng.random() > p_keep:
            G.remove_edge(*e)
            if not nx.is_connected(G):
                G.add_edge(*e)
    # relabel to ints
    mapping = {v: i for i, v in enumerate(sorted(G.nodes()))}
    G = nx.relabel_nodes(G, mapping)
    # add some pendant vertices (degree 1) to create bridges
    n0 = G.number_of_nodes()
    for k in range(rng.randint(0, 3)):
        v = rng.randrange(n0)
        G.add_edge(v, n0 + k)
    return G


def faces_of(emb):
    seen = set()
    F = {}  # half-edge -> face id
    faces = []
    for v in emb.nodes():
        for w in emb.neighbors_cw_order(v):
            if (v, w) in seen:
                continue
            walk = []
            a, b = v, w
            while (a, b) not in seen:
                seen.add((a, b))
                walk.append((a, b))
                a, b = emb.next_face_half_edge(a, b)
            fid = len(faces)
            for h in walk:
                F[h] = fid
            faces.append(walk)
    return faces, F


def build_ghat(G, emb, lam, M, skipR=frozenset(), Cweight=None):
    """lam: dict dart(u,v)->length. Returns nodes, arcs, corner map.
    corner id: ('c', fid, j) = corner at head of walk[j] between walk[j] and walk[j+1].
    """
    faces, F = faces_of(emb)
    nodes = []
    arcs = []
    corner_in = {}   # (half-edge arriving x->v) -> corner node (corner after arriving)
    corner_out = {}  # (half-edge leaving v->y) -> corner node (corner before leaving)
    corner_vertex = {}
    for fid, walk in enumerate(faces):
        k = len(walk)
        for j in range(k):
            c = ('c', fid, j)
            nodes.append(c)
            corner_in[walk[j]] = c
            corner_out[walk[(j + 1) % k]] = c
            corner_vertex[c] = walk[j][1]
        for j in range(k):
            a, b = ('c', fid, j), ('c', fid, (j + 1) % k)
            # E_R edge, both arcs 0 (maps to primal edge walk[j+1])
            h = walk[(j + 1) % k]
            if frozenset(h) in skipR:
                continue
            arcs.append((a, b, 0)); arcs.append((b, a, 0))
    # star centres
    for v in G.nodes():
        nodes.append(('s', v))
    for c, v in corner_vertex.items():
        arcs.append((('s', v), c, M)); arcs.append((c, ('s', v), M))
    # E_C: for each primal edge {u,v}, at endpoint v = max id
    for (u, v) in G.edges():
        if u > v:
            u, v = v, u
        # endpoint v; the two corners at v adjacent to edge vu:
        cA = corner_out[(v, u)]   # corner in face F(v->u)
        cB = corner_in[(u, v)]    # corner in face F(u->v)
        # dart d=(v->u): F(d)=F(v,u) -> F(u,v): cA -> cB with lam[(v,u)]
        if Cweight is not None and frozenset((u, v)) in Cweight:
            arcs.append((cA, cB, Cweight[frozenset((u, v))])); arcs.append((cB, cA, Cweight[frozenset((u, v))]))
            continue
        arcs.append((cA, cB, lam[(v, u)]))
        # dart d=(u->v): F(u,v) -> F(v,u): cB -> cA with lam[(u,v)]
        arcs.append((cB, cA, lam[(u, v)]))
    return nodes, arcs, faces, F, corner_in, corner_out


def dual_graph(G, faces, F, lam):
    nodes = list(range(len(faces)))
    arcs = []
    for (u, v) in G.edges():
        for d in [(u, v), (v, u)]:
            arcs.append((F[d], F[(d[1], d[0])], lam[d]))
    return nodes, arcs


def test_lemmaD(trials, rng):
    bad = 0
    for t in range(trials):
        G = random_planar(rng.randint(2, 5), rng.randint(2, 5), rng.uniform(0.3, 0.9), rng)
        ok, emb = nx.check_planarity(G)
        assert ok
        lam = {}
        for (u, v) in G.edges():
            lam[(u, v)] = rng.randint(-3, 10)
            lam[(v, u)] = rng.randint(-3, 10)
        maxl = max(abs(x) for x in lam.values()) or 1
        nodesH, arcsH, faces, F, ci, co = build_ghat(G, emb, lam, 0)
        M = 2 * (len(nodesH)) * maxl + 1
        nodesH, arcsH, faces, F, ci, co = build_ghat(G, emb, lam, M)
        # planarity of Ghat
        H = nx.Graph()
        H.add_nodes_from(nodesH)
        for a, b, w in arcsH:
            if a != b:
                H.add_edge(a, b)
        assert nx.check_planarity(H)[0], 'Ghat not planar'
        nD, aD = dual_graph(G, faces, F, lam)
        negD = has_neg_cycle(nD, aD)
        negH = has_neg_cycle(nodesH, arcsH)
        if negD != negH:
            bad += 1
            print('NEG CYCLE MISMATCH', negD, negH)
            continue
        if negD:
            continue
        # distances from each face, compare from each corner
        for g in range(len(faces)):
            dD = bellman_ford(nD, aD, g)
            src = ('c', g, 0)
            dH = bellman_ford(nodesH, arcsH, src)
            for c in nodesH:
                if c[0] != 'c':
                    continue
                h = c[1]
                if dD[h] < INF:
                    if dH[c] != dD[h]:
                        bad += 1
                        print('DIST MISMATCH', g, h, dD[h], dH[c])
                else:
                    if dH[c] < M / 2:
                        bad += 1
                        print('SPURIOUS', g, h, dH[c])
    print('lemma D trials', trials, 'bad', bad)


def bfs_dart_path(G, s, t):
    path = nx.shortest_path(G, s, t)
    return [(path[i], path[i + 1]) for i in range(len(path) - 1)]


def make_directed(G, rng):
    cap = {}
    for (u, v) in G.edges():
        if rng.random() < 0.5:
            u, v = v, u
        c = rng.randint(0, 9)
        cap[(u, v)] = c
        cap[(v, u)] = 0 if rng.random() < 0.7 else rng.randint(0, 9)  # sometimes antiparallel capacity
    return cap


def maxflow_ref(G, cap, s, t):
    D = nx.DiGraph()
    D.add_nodes_from(G.nodes())
    for (u, v), c in cap.items():
        if c > 0:
            D.add_edge(u, v, capacity=c)
    return nx.maximum_flow_value(D, s, t) if s != t else 0


def check_flow(G, cap, flow, s, t, value):
    for d, f in flow.items():
        if f > cap[d] or f < -cap[(d[1], d[0])]:
            return 'cap violated %s f=%s c=%s rc=%s' % (d, f, cap[d], cap[(d[1], d[0])])
        if flow[(d[1], d[0])] != -f:
            return 'antisym'
    for v in G.nodes():
        net = sum(flow[(v, w)] for w in G.neighbors(v))
        exp = value if v == s else (-value if v == t else 0)
        if net != exp:
            return 'conservation at %s: %s vs %s' % (v, net, exp)
    return None


def test_thmC(trials, rng):
    bad = 0
    for tr in range(trials):
        G = random_planar(rng.randint(2, 5), rng.randint(2, 5), rng.uniform(0.3, 0.9), rng)
        ok, emb = nx.check_planarity(G)
        cap = make_directed(G, rng)
        s, t = rng.sample(list(G.nodes()), 2)
        ref = maxflow_ref(G, cap, s, t)
        P = bfs_dart_path(G, s, t)
        Pset = set(P)
        Prev = set((b, a) for a, b in P)

        def feasible(lmb):
            lam = {}
            for d in cap:
                f0 = lmb if d in Pset else (-lmb if d in Prev else 0)
                lam[d] = cap[d] - f0
            maxl = max(abs(x) for x in lam.values()) or 1
            nodesH, arcsH, faces, F, ci, co = build_ghat(G, emb, lam, 0)
            M = 2 * len(nodesH) * maxl + 1
            nodesH, arcsH, faces, F, ci, co = build_ghat(G, emb, lam, M)
            if has_neg_cycle(nodesH, arcsH):
                return None
            dH = bellman_ford(nodesH, arcsH, ('c', 0, 0))
            phi = {g: dH[('c', g, 0)] for g in range(len(faces))}
            # all corners of a face must agree
            for c in nodesH:
                if c[0] == 'c' and dH[c] != phi[c[1]]:
                    return 'corner-disagree'
            flow = {}
            for d in cap:
                f0 = lmb if d in Pset else (-lmb if d in Prev else 0)
                flow[d] = phi[F[(d[1], d[0])]] - phi[F[d]] + f0
            return flow

        lo, hi = 0, sum(cap.values()) + 1
        # find largest feasible
        while lo < hi:
            mid = (lo + hi + 1) // 2
            r = feasible(mid)
            if r is None:
                hi = mid - 1
            else:
                lo = mid
        flow = feasible(lo)
        err = check_flow(G, cap, flow, s, t, lo)
        if lo != ref or err:
            bad += 1
            print('THM C FAIL', lo, ref, err)
    print('thm C trials', trials, 'bad', bad)


def test_thmCprime(trials, rng):
    bad = 0
    done = 0
    for tr in range(trials):
        G = random_planar(rng.randint(2, 5), rng.randint(2, 5), rng.uniform(0.3, 0.9), rng)
        ok, emb = nx.check_planarity(G)
        cap = make_directed(G, rng)
        faces, F = faces_of(emb)
        fid = rng.randrange(len(faces))
        walk = faces[fid]
        k = len(walk)
        js = rng.randrange(k)
        cand = [j for j in range(k) if walk[j][1] != walk[js][1]]
        if not cand:
            continue
        jt = rng.choice(cand)
        s, t = walk[js][1], walk[jt][1]
        if G.has_edge(s, t):
            continue  # keep simple graph for nx embedding
        x, xp = walk[js][0], walk[jt][0]
        ref = maxflow_ref(G, cap, s, t)
        # insert chord t->s inside face fid: at s ccw of x, at t ccw of xp
        emb2 = nx.PlanarEmbedding()
        emb2.add_nodes_from(emb.nodes())
        for v in emb.nodes():
            for w in emb.neighbors_cw_order(v):
                emb2.add_half_edge(v, w) if False else None
        emb2 = emb.copy()
        emb2.add_half_edge_ccw(s, t, x)
        emb2.add_half_edge_ccw(t, s, xp)
        emb2.check_structure()
        G2 = G.copy(); G2.add_edge(s, t)
        lam = dict(cap)
        lam[(t, s)] = 0; lam[(s, t)] = 0
        nodesH, arcsH, faces2, F2, ci, co = build_ghat(G2, emb2, lam, 0)
        maxl = max(abs(x_) for x_ in lam.values()) or 1
        M = 2 * len(nodesH) * maxl + 1
        nodesH, arcsH, faces2, F2, ci, co = build_ghat(G2, emb2, lam, M, skipR=frozenset([frozenset((s, t))]), Cweight={frozenset((s, t)): M})
        f1, f2 = F2[(t, s)], F2[(s, t)]
        assert f1 != f2
        # source: any corner of f1
        dH = bellman_ford(nodesH, arcsH, ('c', f1, 0))
        # corners of each face agree?
        phi = {}
        for c in nodesH:
            if c[0] == 'c':
                phi.setdefault(c[1], dH[c])
                if phi[c[1]] != dH[c]:
                    print('corner disagreement in face', c[1]); bad += 1
        val = phi[f2] - phi[f1]
        flow = {}
        for d in cap:
            flow[d] = phi[F2[(d[1], d[0])]] - phi[F2[d]]
        err = check_flow(G, cap, flow, s, t, val)
        done += 1
        if val != ref or err:
            bad += 1
            print("THM C' FAIL", val, ref, err)
    print("thm C' trials", done, 'bad', bad)


if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    test_lemmaD(150, rng)
    test_thmC(150, rng)
    test_thmCprime(300, rng)
