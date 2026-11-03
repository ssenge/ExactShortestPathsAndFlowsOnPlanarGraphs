"""Sanity check of monge_lp: terminals on ONE face => alpha*(face order) = 1 (G4), in both
orientations; random pruned-Delaunay planar digraphs, terminals = up to 7 vertices of one face."""
import sys, numpy as np, networkx as nx
sys.path.insert(0, '.')
from rot import monge_lp
from r4_euler import rand_plane
rng = np.random.default_rng(3)
bad = 0; n = 0
for t in range(150):
    P = rand_plane(int(rng.integers(10, 30)), rng.random() * 0.6, rng)
    faces, df = P.faces()
    f = max(faces, key=len)
    order = []
    for v, _ in f:
        if v not in order: order.append(v)
    if len(order) < 4: continue
    k = min(len(order), 7); start = int(rng.integers(len(order)))
    idx = sorted(rng.choice(len(order), k, replace=False))
    T = [order[i] for i in idx]
    P.w = {(e, di): int(rng.integers(1, 50)) for e in P.edges for di in (0, 1)}
    sp = dict(nx.all_pairs_dijkstra_path_length(P.digraph()))
    delta = {(a, b): sp[a][b] for a in T for b in T if a != b}
    for o in (T, T[::-1]):
        n += 1
        a = monge_lp(delta, o)[1]
        bad += a > 1 + 1e-7
print('one-face instances: %d LPs, alpha*>1 in %d' % (n, bad))
