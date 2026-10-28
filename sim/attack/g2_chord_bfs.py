"""Chord attack, BFS-consistent version.  BFS tree from r; root separator S = fundamental cycle
r-a1-a2 + r-b1-b2 + closing edge a2-b2.  a1-b1 is a non-tree edge between same-level vertices
on the two branches: a chord of S, drawn INSIDE S.  Exterior child X2 (Li-Parter: S_i = S since
the exterior is connected) has G[X2] = induced, which contains the chord inside its hole."""
import sys, numpy as np, networkx as nx
sys.path.insert(0, '.')
from rot import Plane, monge_lp, all_cyclic_orders
pos = {'r': (0, 2), 'a1': (-1, 1), 'b1': (1, 1), 'a2': (-1, -1), 'b2': (1, -1), 'z': (0, 0),
       'y1': (-3, 0), 'y2': (3, 0), 'y3': (0, -3)}
E = [('r', 'a1'), ('a1', 'a2'), ('r', 'b1'), ('b1', 'b2'), ('a2', 'b2'), ('a1', 'b1'),
     ('z', 'a1'), ('z', 'a2'), ('z', 'b1'), ('z', 'b2'),
     ('y1', 'r'), ('y1', 'a1'), ('y1', 'a2'), ('y2', 'r'), ('y2', 'b1'), ('y2', 'b2'),
     ('y3', 'a2'), ('y3', 'b2'), ('y3', 'y1'), ('y3', 'y2')]
P = Plane.from_coords(pos, E)
V, Ec, F = P.euler(); print('G: V-E+F =', V - Ec + F)
U = nx.Graph(E); lvl = nx.single_source_shortest_path_length(U, 'r')
print('BFS levels:', lvl, '| tree path a2..r..b2 monotone:',
      lvl['a2'] > lvl['a1'] > lvl['r'] < lvl['b1'] < lvl['b2'], '| chord a1-b1 same level:', lvl['a1'] == lvl['b1'])
S = ['r', 'a1', 'a2', 'b2', 'b1']
X2 = S + ['y1', 'y2', 'y3']
G2 = P.induced(X2)
fv = G2.face_vertices()
print('faces of G[X2] containing all of J=S:', [i for i, f in enumerate(fv) if set(S) <= f])
print('faces of G[X2] meeting S in >=3:', [sorted(f & set(S)) for f in fv if len(f & set(S)) >= 3])
rng = np.random.default_rng(2)
cnt = 0; worst = 1
for t in range(100):
    G2.w = {(e, di): int(rng.integers(1, 30)) for e in G2.edges for di in (0, 1)}
    sp = dict(nx.all_pairs_dijkstra_path_length(G2.digraph()))
    delta = {(x, y): sp[x][y] for x in S for y in S if x != y}
    m = min(monge_lp(delta, o)[1] for o in all_cyclic_orders(S))
    cnt += m > 1 + 1e-9; worst = max(worst, m)
print('random weights: %d/100 with no cyclic order at alpha*=1; max min_sigma alpha* = %.4f' % (cnt, worst))
