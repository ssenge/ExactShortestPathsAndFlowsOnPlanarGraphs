"""Sequential checks of the combinatorial claims in NOTES.md (exact arithmetic, small random instances).

1. Lemma V: on a recursive separator decomposition with per-bag G[X]-distances to hubs, the
   per-bag convergecast formula gives exact virtual-source distances. Also counts how often the
   single-bag label query (lowest separating bag only) is wrong, while the all-bags query is exact.
2. Lemma D: weighted face-disjoint graph Ĝ (E_R = 0, E_C = dual dart lengths, E_S = M) gives
   dual distances and the same negative cycles as G*; Ĝ is planar with diameter <= 3D.
3. Theorem C: Miller–Naor binary search with negative-cycle tests on Ĝ finds the max-flow value,
   and the potential-based assignment is a feasible flow of that value.
4. Theorem C': Hassin with a chord in a face shared by s and t, on Ĝ with the chord's E_R/E_C
   edges removed, gives a feasible max flow.

usage: python3 check.py [instances] [seed]
"""
import random
import sys

import networkx as nx
from scipy.spatial import Delaunay

INF = float("inf")


def planar_instance(n, rng):
    pts = [(rng.random(), rng.random()) for _ in range(n)]
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for a, b, c in Delaunay(pts).simplices:
        G.add_edges_from([(a, b), (b, c), (a, c)])
    for e in rng.sample(list(G.edges), len(G.edges) // 3):
        G.remove_edge(*e)
        if not nx.is_connected(G):
            G.add_edge(*e)
    return G


def dijkstra_multi(D, phi):
    """min_u phi(u) + dist_D(u, v); D is a DiGraph with nonnegative 'w'."""
    H = D.copy()
    H.add_node("σ")
    for u, x in phi.items():
        if x < INF and u in H:
            H.add_edge("σ", u, w=x)
    d = nx.single_source_dijkstra_path_length(H, "σ", weight="w")
    return {v: d.get(v, INF) for v in D}


# ---------- 1. Lemma V ----------

def decompose(U, X, anc, rng, leaf, out):
    """Recursive vertex-separator decomposition; returns the bag index. Bag: dict X, hubs, S, kids.
    Children are C ∪ S for each component C of U[X] - S, so every path in G[X] between different
    children meets S, and a non-separator vertex lies in exactly one child."""
    sub = U.subgraph(X)
    root = rng.choice(sorted(X))
    lay = nx.single_source_shortest_path_length(sub, root)
    md = max(lay.values())
    i = len(out)
    if len(X) <= leaf or md < 2:
        out.append(dict(X=X, hubs=anc & X, S=set(), kids=[]))
        return i
    k = rng.randint(1, md - 1)
    S = {v for v, l in lay.items() if l == k}
    out.append(dict(X=X, hubs=(anc & X) | S, S=S, kids=[]))
    for C in nx.connected_components(sub.subgraph(X - S)):
        out[i]["kids"].append(decompose(U, C | S, (anc & X) | S, rng, leaf, out))
    return i


def lowest_separating(bags, u, v):
    """The top-most bag where u, v lie in different children or one lies on S (query of [1], Thm 4)."""
    i = 0
    while bags[i]["kids"]:
        b = bags[i]
        if u in b["S"] or v in b["S"]:
            return i
        cu = next(j for j in b["kids"] if u in bags[j]["X"])
        cv = next(j for j in b["kids"] if v in bags[j]["X"])
        if cu != cv:
            return i
        i = cu
    return None


def check_lemma_v(G, rng):
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for u, v in G.edges:
        for a, b in ((u, v), (v, u)):
            if rng.random() < 0.7:
                D.add_edge(a, b, w=rng.choice([0, 0, 1, 2, 3, 5, 8, 13]))
    bags = []
    decompose(G, set(G), set(), rng, 8, bags)
    R = D.reverse()
    to_h, from_h = [], []  # per bag: d_X(u,h) and d_X(h,v)
    for b in bags:
        sx, rx = D.subgraph(b["X"]), R.subgraph(b["X"])
        from_h.append({h: nx.single_source_dijkstra_path_length(sx, h, weight="w") for h in b["hubs"]})
        to_h.append({h: nx.single_source_dijkstra_path_length(rx, h, weight="w") for h in b["hubs"]})
    phi = {u: (rng.randint(0, 30) if rng.random() < 0.2 else INF) for u in D}
    phi[rng.choice(list(D))] = 0
    truth = dijkstra_multi(D, phi)
    est = {v: INF for v in D}
    for i, b in enumerate(bags):
        X, H = b["X"], b["hubs"]
        if not b["kids"]:
            loc = dijkstra_multi(D.subgraph(X), {u: phi[u] for u in X})
            for v in X:
                est[v] = min(est[v], loc[v])
        A = {h: min(phi[u] + to_h[i][h].get(u, INF) for u in X) for h in H}
        for v in X:
            for h in H:
                est[v] = min(est[v], A[h] + from_h[i][h].get(v, INF))
    assert est == truth, "Lemma V formula differs from true virtual-source distances"

    # pairwise label query: all common bags (exact) vs the single lowest separating bag
    bad_single = 0
    pairs = [tuple(rng.sample(list(D), 2)) for _ in range(60)]
    for u, v in pairs:
        true = nx.shortest_path_length(D, u, v, weight="w") if nx.has_path(D, u, v) else INF
        q_all = INF
        for i, b in enumerate(bags):
            if u not in b["X"] or v not in b["X"]:
                continue
            if not b["kids"]:
                sx = D.subgraph(b["X"])
                if nx.has_path(sx, u, v):
                    q_all = min(q_all, nx.shortest_path_length(sx, u, v, weight="w"))
            for h in b["hubs"]:
                q_all = min(q_all, to_h[i][h].get(u, INF) + from_h[i][h].get(v, INF))
        assert q_all == true, "all-bags label query is not exact"
        i = lowest_separating(bags, u, v)
        if i is not None:
            q1 = min((to_h[i][h].get(u, INF) + from_h[i][h].get(v, INF) for h in bags[i]["hubs"]), default=INF)
            assert q1 >= true
            bad_single += q1 != true
    return bad_single, len(pairs)


# ---------- 2. Lemma D: weighted face-disjoint graph ----------

def faces_of(E):
    face, faces = {}, []
    for v, w in E.edges:
        if (v, w) not in face:
            walk, h = [], (v, w)
            while h not in face:
                face[h] = len(faces)
                walk.append(h)
                h = E.next_face_half_edge(*h)
            faces.append(walk)
    return face, faces


def arc(Gr, a, b, x):
    """Ĝ is a multigraph (e.g. both edges at a degree-2 vertex give E_C edges between the same two
    corners); for distances only the lightest parallel arc matters."""
    if not Gr.has_edge(a, b) or Gr[a][b]["w"] > x:
        Gr.add_edge(a, b, w=x)


def ghat(E, lam, M, drop=()):
    """Weighted Ĝ. Corner = outgoing half-edge (v,w) (the angle at v before leaving to w).
    lam[(v,w)] = length of dual dart F(v,w) -> F(w,v). `drop`: primal edges whose E_R/E_C edges are omitted."""
    Gh = nx.DiGraph()
    for v, w in E.edges:
        arc(Gh, ("s", v), ("c", v, w), M)
        arc(Gh, ("c", v, w), ("s", v), M)
    for v, w in E.edges:
        if frozenset((v, w)) in drop:
            continue
        x = E.next_face_half_edge(v, w)[1]  # E_R along edge vw inside face F(v,w)
        arc(Gh, ("c", v, w), ("c", w, x), 0)
        arc(Gh, ("c", w, x), ("c", v, w), 0)
        if v > w:  # E_C at the larger endpoint v
            y = E.next_face_half_edge(w, v)[1]  # corner (v,y) lies in F(w,v)
            arc(Gh, ("c", v, w), ("c", v, y), lam[(v, w)])
            arc(Gh, ("c", v, y), ("c", v, w), lam[(w, v)])
    return Gh


def dual(E, lam, face):
    Ds = nx.DiGraph()
    Ds.add_nodes_from(set(face.values()))
    neg_loop = False
    for (v, w), x in lam.items():
        a, b = face[(v, w)], face[(w, v)]
        if a == b:
            neg_loop |= x < 0
        elif not Ds.has_edge(a, b) or Ds[a][b]["w"] > x:
            Ds.add_edge(a, b, w=x)
    return Ds, neg_loop


def bf(Gr, src):
    """Bellman–Ford distances, or None on a negative cycle reachable from src."""
    try:
        return nx.single_source_bellman_ford_path_length(Gr, src, weight="w")
    except nx.NetworkXUnbounded:
        return None


def check_lemma_d(G, E, rng):
    face, faces = faces_of(E)
    if rng.random() < 0.5:  # arbitrary signs: usually has negative cycles
        lam = {h: rng.randint(-3, 9) for h in E.edges}
    else:  # reduced costs of nonnegative lengths: negative arcs, no negative cycle
        pi = {f: rng.randint(0, 6) for f in range(len(faces))}
        lam = {(v, w): rng.randint(0, 3) + pi[face[(v, w)]] - pi[face[(w, v)]] for v, w in E.edges}
    M = 2 * (len(G) + 4 * len(G.edges)) * 10 + 1
    Gh = ghat(E, lam, M)
    U = Gh.to_undirected()
    assert nx.check_planarity(U)[0], "Ĝ not planar"
    assert nx.diameter(U) <= 3 * nx.diameter(G), "Ĝ diameter > 3D"
    Ds, neg_loop = dual(E, lam, face)
    src = faces[0][0]  # a corner of face 0
    dh = bf(Gh, ("c",) + src)  # every node of Ĝ is reachable through E_S
    neg_dual = not _dual_neg_cycle_free(Ds, neg_loop)
    assert neg_dual == (dh is None), "negative cycles of Ĝ and G* differ"
    if neg_dual:
        return "neg"
    dd = bf(Ds, 0)
    for h, f in face.items():
        exp = dd.get(f, INF)
        got = dh[("c",) + h]
        assert (exp == got) if exp < INF else got >= M // 2, "Ĝ distance != dual distance"
    return "ok"


def _dual_neg_cycle_free(Ds, neg_loop):
    if neg_loop:
        return False
    H = Ds.copy()
    for f in list(Ds):
        H.add_edge("z", f, w=0)
    return bf(H, "z") is not None


# ---------- 3. Theorem C: Miller–Naor on Ĝ ----------

def capacities(G, rng):
    cap = {}
    for u, v in G.edges:
        a, b = rng.randint(0, 9), rng.randint(0, 9)
        if rng.random() < 0.3:  # some one-directional edges
            a, b = (a, 0) if rng.random() < 0.5 else (0, b)
        cap[(u, v)], cap[(v, u)] = a, b
    return cap


def flow_from_potential(E, face_pot, extra):
    return {(v, w): face_pot[(w, v)] - face_pot[(v, w)] + extra.get((v, w), 0) for v, w in E.edges}


def check_flow(f, cap, s, t, value, nodes):
    for d, x in f.items():
        assert x <= cap[d], "capacity violated"
        assert x == -f[(d[1], d[0])], "not antisymmetric"
    for v in nodes:
        net = sum(x for (a, _), x in f.items() if a == v)
        assert net == (value if v == s else -value if v == t else 0), "conservation violated"


def check_miller_naor(G, E, rng):
    cap = capacities(G, rng)
    s, t = rng.sample(list(G), 2)
    Dg = nx.DiGraph()
    Dg.add_nodes_from(G)
    for (u, v), c in cap.items():
        if c:
            Dg.add_edge(u, v, capacity=c)
    true = nx.maximum_flow_value(Dg, s, t)
    path = nx.shortest_path(G, s, t)
    P = set(zip(path, path[1:]))
    M = 2 * (len(G) + 4 * len(G.edges)) * (20 * len(G) + 10) + 1

    def test(lam_val):
        lam = {d: cap[d] - lam_val * (d in P) + lam_val * ((d[1], d[0]) in P) for d in E.edges}
        src = ("c",) + next(iter(E.edges))
        return bf(ghat(E, lam, M), src)

    lo, hi = 0, sum(cap[(s, x)] for x in G[s])  # feasible(lo), search the largest feasible
    while lo < hi:
        mid = (lo + hi + 1) // 2
        lo, hi = (mid, hi) if test(mid) is not None else (lo, mid - 1)
    assert lo == true, f"Miller–Naor value {lo} != max flow {true}"
    d = test(lo)
    pot = {h: d[("c",) + h] for h in E.edges}
    extra = {}
    for a, b in P:
        extra[(a, b)] = extra.get((a, b), 0) + lo
        extra[(b, a)] = extra.get((b, a), 0) - lo
    check_flow(flow_from_potential(E, pot, extra), cap, s, t, lo, G)
    return true


# ---------- 4. Theorem C': chord in a shared face ----------

def check_hassin(G, E, rng):
    face, faces = faces_of(E)
    walk = max(faces, key=len)
    verts = [h[0] for h in walk]
    s, t = rng.sample(sorted(set(verts)), 2)
    if G.has_edge(s, t):
        return None
    p = walk[(verts.index(s) - 1) % len(walk)][0]  # half-edge (p, s) precedes (s, .) in the walk
    q = walk[(verts.index(t) - 1) % len(walk)][0]
    E2 = nx.PlanarEmbedding()
    E2.set_data(E.get_data())
    E2.add_half_edge(s, t, cw=p)
    E2.add_half_edge(t, s, cw=q)
    E2.check_structure()
    cap = capacities(G, rng)
    Dg = nx.DiGraph()
    Dg.add_nodes_from(G)
    for (u, v), c in cap.items():
        if c:
            Dg.add_edge(u, v, capacity=c)
    true = nx.maximum_flow_value(Dg, s, t)
    M = 10 ** 6
    lam = dict(cap)
    lam[(s, t)] = lam[(t, s)] = M
    Gh = ghat(E2, lam, M, drop={frozenset((s, t))})
    d = bf(Gh, ("c", t, s))  # source: corner of face F(t,s)
    pot = {h: d[("c",) + h] for h in E2.edges}
    f = flow_from_potential(E2, pot, {})
    value = f[(t, s)]
    assert value == true, f"Hassin value {value} != max flow {true}"
    del f[(s, t)], f[(t, s)]
    check_flow(f, cap, s, t, value, G)
    return true


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    bad = tot = 0
    stats = {"ok": 0, "neg": 0}
    flows, hassin = [], 0
    for _ in range(k):
        G = planar_instance(rng.randint(25, 60), rng)
        E = nx.check_planarity(G)[1]
        b, p = check_lemma_v(G, rng)
        bad, tot = bad + b, tot + p
        stats[check_lemma_d(G, E, rng)] += 1
        flows.append(check_miller_naor(G, E, rng))
        hassin += check_hassin(G, E, rng) is not None
    print(f"Lemma V exact on {k} instances; single-bag query wrong on {bad}/{tot} pairs (all-bags query exact)")
    print(f"Lemma D: {stats['ok']} instances distances equal, {stats['neg']} with matching negative cycles")
    print(f"Thm C: Miller–Naor on Ĝ = max flow on {k} instances (values {flows})")
    print(f"Thm C': Hassin on Ĝ = max flow on {hassin} instances")


if __name__ == "__main__":
    main()
