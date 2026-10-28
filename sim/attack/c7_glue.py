"""Attack (c): for children C u (S n N(C)) (components construction), (7c) fails and then
Glue(G[X_i]; ~_G) != G[X] (R2(a)), so H_X overestimates hub distances by more than 1+eps.
Same random instances as l16.py (COMP mode)."""
import numpy as np, networkx as nx, math
from scipy.spatial import Delaunay
exec(open('l16.py').read().split("stats = {")[0])     # reuse imports + inside()
rng = np.random.default_rng(21)
inst = viol = 0; worst = 1
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
    cyc = nx.shortest_path(T, a, b); S = set(cyc)
    poly = [tuple(pts[v]) for v in cyc]
    interior = {v for v in range(n) if v not in S and inside(tuple(pts[v]), poly)}
    exterior = set(range(n)) - S - interior
    children = []
    for R in (interior, exterior):
        for C in nx.connected_components(U.subgraph(R)):
            children.append(set(C) | {s for s in S if any(U.has_edge(s, c) for c in C)})
    Gl = nx.DiGraph()
    for Ch in children: Gl.add_edges_from(D.subgraph(Ch).edges(data=True))
    inst += 1
    dX = dict(nx.all_pairs_dijkstra_path_length(D)); dG = dict(nx.all_pairs_dijkstra_path_length(Gl))
    r = max((dG.get(x, {}).get(y, math.inf) / dX[x][y]) for x in S for y in S if x != y)
    viol += r > 1 + 1e-9; worst = max(worst, r)
print('instances %d; glued children overestimate some hub distance in %d; worst ratio %s' % (inst, viol, worst))
