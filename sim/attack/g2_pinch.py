"""Attack (b)/(G2): two holes of X that touch at one vertex u (ancestor separators S1, S2 with
S1 n S2 = {u}).  Def. 6 step 3 is skipped because (P u dS*) n S = {u} is non-empty, so P_X
has no path between them and O_X = G[X]; the two holes stay two faces.
X = inside square S1=(o0,o1,o2,o3), outside triangle S2=(o0,a,b); u=o0.  J_X = S1 u S2."""
import sys, numpy as np, networkx as nx
sys.path.insert(0, '.')
from rot import Plane, monge_lp, all_cyclic_orders
pos = {'o0': (2, 0), 'o1': (0, 2), 'o2': (-2, 0), 'o3': (0, -2), 'a': (1, 0.4), 'b': (1, -0.4),
       'm': (-0.5, 0), 'n1': (0.3, 1), 'n2': (0.3, -1)}
E = [('o0', 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o3', 'o0'), ('o0', 'a'), ('a', 'b'), ('b', 'o0'),
     ('a', 'n1'), ('n1', 'o1'), ('b', 'n2'), ('n2', 'o3'), ('m', 'o2'), ('m', 'a'), ('m', 'b'),
     ('m', 'n1'), ('m', 'n2'), ('n1', 'o0'), ('n2', 'o0')]
P = Plane.from_coords(pos, E)
V, Ec, F = P.euler(); print('V-E+F =', V - Ec + F)
J = ['o0', 'o1', 'o2', 'o3', 'a', 'b']
fv = P.face_vertices()
print('faces containing all of J_X:', [i for i, f in enumerate(fv) if set(J) <= f])
print('faces meeting J_X in >=3:', [sorted(f & set(J)) for f in fv if len(f & set(J)) >= 3])
rng = np.random.default_rng(11)
cnt = 0; worst = 1
for t in range(60):
    P.w = {(e, di): int(rng.integers(1, 30)) for e in P.edges for di in (0, 1)}
    sp = dict(nx.all_pairs_dijkstra_path_length(P.digraph()))
    delta = {(x, y): sp[x][y] for x in J for y in J if x != y}
    m = min(monge_lp(delta, o)[1] for o in all_cyclic_orders(J))
    cnt += m > 1 + 1e-9; worst = max(worst, m)
print('random weights: %d/60 with no cyclic order at alpha*=1; max over instances of min_sigma alpha* = %.4f' % (cnt, worst))
