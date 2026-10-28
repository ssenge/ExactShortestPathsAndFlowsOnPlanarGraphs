"""Attack (b)/(G2): G[X] is the INDUCED subgraph, so a chord of an ancestor separator that is
drawn inside the hole is an edge of G[X] and splits the hole into several faces.
Then J_X is not on one face of O_X, (I1) fails already at a leaf, and the LP of Lemma R5 can
be infeasible for every cyclic order.

G: hexagon S = s0..s5 (root separator, real closing edge s5-s0), hub z inside adjacent to all
s_i, chord s0-s3 drawn OUTSIDE S (over s1,s2), w1 outside under the chord adjacent to s1,s2,
w2 outside adjacent to s4,s5.  Interior child L = {s0..s5, z} (closed interior; Li-Parter's
X1 contains all of S).  G[L] = wheel + chord.  P_L = {} (child of root), J_L = S.
"""
import sys, itertools, math
import numpy as np
sys.path.insert(0, '.')
from rot import Plane, monge_lp, all_cyclic_orders
import networkx as nx

P = Plane()
def E(a, b):
    e = P.new_eid(); P.edges[e] = (a, b); return e
s = ['s%d' % i for i in range(6)]
cyc = [E(s[i], s[(i + 1) % 6]) for i in range(6)]      # cyc[i] = s_i - s_{i+1}
spk = [E('z', s[i]) for i in range(6)]
ch = E('s0', 's3')
w1a, w1b = E('w1', 's1'), E('w1', 's2')
w2a, w2b = E('w2', 's4'), E('w2', 's5')
# ccw rotations (hexagon s_i at angle 60 i deg, z at origin, chord arcs over the top)
P.rot['z'] = spk[:]                                       # angles 0,60,...,300
P.rot['s0'] = [ch, cyc[0], spk[0], cyc[5]]                # chord ~60, s1 120, z 180, s5 240
P.rot['s1'] = [w1a, cyc[1], spk[1], cyc[0]]               # out ~90?, s2 180, z 240, s0 300
P.rot['s2'] = [cyc[1], w1b, cyc[2], spk[2]]
P.rot['s3'] = [spk[3], cyc[2], ch, cyc[3]]                # z 0, s2 60, chord 120, s4 300
P.rot['s4'] = [cyc[4], spk[4], cyc[3], w2a]
P.rot['s5'] = [cyc[5], spk[5], cyc[4], w2b]
P.rot['w1'] = [w1b, w1a]
P.rot['w2'] = [w2a, w2b]
V, Ecnt, F = P.euler()
print('G: V-E+F =', V - Ecnt + F, ' (must be 2 for a valid plane embedding)')
L = P.induced(s + ['z'])
V, Ecnt, F = L.euler(); print('G[L]: V-E+F =', V - Ecnt + F)
fv = L.face_vertices()
J = set(s)
print('faces of G[L] containing all of J_L:', [i for i, f in enumerate(fv) if J <= f])
print('faces of G[L] meeting J_L in >=3 terminals:', [sorted(f & J) for f in fv if len(f & J) >= 3])

# adversarial weights (W1: integers >=1; W2: every edge has both directions)
M = 100
cheap = {('s1', 's0'), ('s0', 's3'), ('s3', 's4'), ('s5', 'z'), ('z', 's2')}
def weights(rng=None):
    L.w = {}
    for e, (a, b) in L.edges.items():
        for di, (t, h) in enumerate(((a, b), (b, a))):
            if rng is None:
                L.w[(e, di)] = 1 if (t, h) in cheap else M
            else:
                L.w[(e, di)] = int(rng.integers(1, 30))
def dists():
    D = L.digraph()
    sp = dict(nx.all_pairs_dijkstra_path_length(D))
    return {(a, b): sp[a][b] for a in s for b in s if a != b}

weights()
delta = dists()
best = min((monge_lp(delta, o)[1], o) for o in all_cyclic_orders(s))
print('adversarial weights: min over all 120 cyclic orders of alpha*(sigma) = %.4f  (order %s)' % best)
st, a, _ = monge_lp(delta, s, fix_alpha=1.05)
print('LP(delta, natural sigma, 1.05) status (2 = infeasible):', st)

rng = np.random.default_rng(7)
cnt = 0; worst = 1
for t in range(60):
    weights(rng)
    delta = dists()
    m = min(monge_lp(delta, o)[1] for o in all_cyclic_orders(s))
    cnt += m > 1 + 1e-9; worst = max(worst, m)
print('random weights 1..29: %d/60 instances where NO cyclic order admits alpha*=1 ; max min-alpha* = %.4f' % (cnt, worst))
