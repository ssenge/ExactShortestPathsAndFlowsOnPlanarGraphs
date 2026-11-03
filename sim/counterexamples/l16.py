"""Lemma 16': random planar digraphs, separator = fundamental cycle of a BFS tree, children
either (LP) Li-Parter style: closed interior X1 + exterior components C u (S n N(C)), or
(COMP) all components C u (S n N(C)) (interior split too).  Random extra hubs dS*_X.
Child labels and delta^H are random overestimates within factors lam1, lam2.
Check dist_{G[X]} <= d~_X <= max(lam1,lam2) * dist_{G[X]} in both directions."""
import numpy as np, networkx as nx, math, sys
sys.path.insert(0, '.')
from scipy.spatial import Delaunay
rng = np.random.default_rng(21)

def inside(pt, poly):
    x, y = pt; c = False
    for i in range(len(poly)):
        (x1, y1), (x2, y2) = poly[i], poly[(i + 1) % len(poly)]
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / (y2 - y1) + x1:
            c = not c
    return c

stats = {'LP': [0, 0, 0], 'COMP': [0, 0, 0]}   # checks, fails, 7c-violations(instances)
for trial in range(300):
    n = int(rng.integers(15, 45)); pts = rng.random((n, 2))
    E = set()
    for s in Delaunay(pts).simplices:
        for i in range(3):
            E.add(tuple(sorted((int(s[i]), int(s[(i + 1) % 3])))))
    U = nx.Graph(); U.add_nodes_from(range(n))
    Tr = nx.minimum_spanning_tree(nx.Graph([(a, b, {'weight': rng.random()}) for a, b in E]))
    U.add_edges_from(Tr.edges()); U.add_edges_from(e for e in E if rng.random() < 0.6)
    D = nx.DiGraph()
    for a, b in U.edges():
        D.add_edge(a, b, weight=int(rng.integers(1, 20))); D.add_edge(b, a, weight=int(rng.integers(1, 20)))
    T = nx.bfs_tree(U, int(rng.integers(n))).to_undirected()
    nontree = [e for e in U.edges() if not T.has_edge(*e)]
    if not nontree: continue
    a, b = nontree[int(rng.integers(len(nontree)))]
    cyc = nx.shortest_path(T, a, b)
    S = set(cyc)
    poly = [tuple(pts[v]) for v in cyc]
    interior = {v for v in range(n) if v not in S and inside(tuple(pts[v]), poly)}
    exterior = set(range(n)) - S - interior
    A = set(int(v) for v in rng.choice(n, int(rng.integers(0, 5)), replace=False))   # dS*_X
    hubs = S | A
    for mode in ('LP', 'COMP'):
        children = []
        regions = [exterior] if mode == 'LP' else [interior, exterior]
        if mode == 'LP':
            children.append(interior | S)
        for R in regions:
            for C in nx.connected_components(U.subgraph(R)):
                children.append(set(C) | {s for s in S if any(U.has_edge(s, c) for c in C)})
        # (7c) check
        viol = any(not any(x in Ch and y in Ch for Ch in children) for x, y in U.edges())
        stats[mode][2] += viol
        lam1, lam2 = 1 + rng.random(), 1 + rng.random()
        dX = dict(nx.all_pairs_dijkstra_path_length(D))
        dH = {(t, h): dX[t][h] * (1 + rng.random() * (lam2 - 1)) for t in hubs for h in hubs if h in dX[t]}
        for Ch in children:
            DC = D.subgraph(Ch)
            dC = dict(nx.all_pairs_dijkstra_path_length(DC))
            hubC = hubs & Ch
            lab_out = {(v, h): dC[v][h] * (1 + rng.random() * (lam1 - 1)) for v in Ch for h in hubC if h in dC[v]}
            lab_in = {(h, v): dC[h][v] * (1 + rng.random() * (lam1 - 1)) for v in Ch for h in hubC if v in dC[h]}
            for v in Ch - hubs:
                if sum(v in C2 for C2 in children) != 1: continue
                for h in hubs:
                    c1 = [lab_out[(v, h)]] if (v, h) in lab_out else []
                    c2 = [lab_out[(v, t)] + dH[(t, h)] for t in S & Ch if (v, t) in lab_out and (t, h) in dH]
                    est = min(c1 + c2, default=math.inf)
                    tru = dX[v].get(h, math.inf)
                    c1 = [lab_in[(h, v)]] if (h, v) in lab_in else []
                    c2 = [dH[(h, t)] + lab_in[(t, v)] for t in S & Ch if (t, v) in lab_in and (h, t) in dH]
                    est2 = min(c1 + c2, default=math.inf); tru2 = dX[h].get(v, math.inf)
                    lam = max(lam1, lam2)
                    for e_, t_ in ((est, tru), (est2, tru2)):
                        stats[mode][0] += 1
                        ok = (t_ - 1e-9 <= e_ <= lam * t_ + 1e-9) or (t_ == math.inf and e_ == math.inf)
                        stats[mode][1] += not ok
for mode, (c, f, v) in stats.items():
    print('%s children: %d (v,h) checks, %d failures; instances violating full (7c): %d' % (mode, c, f, v))
