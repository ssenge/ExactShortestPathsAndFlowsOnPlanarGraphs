"""The smallest instances quoted in REPORT.md, each recomputed here."""
import collections
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
import a6_flow

rng = random.Random(1)

# 1. Two vertices, one arc, removed by the decomposition: equal labels in the reading of Cor. 33 on G minus E_rem
n, arcs = 2, [(0, 1, 1)]
seen = collections.Counter()
for _ in range(2000):
    er = ldd(n, arcs, 2, rng, 1.0, st=Stats())
    kept = [a for i, a in enumerate(arcs) if i not in er]
    r = alg3(n, kept, rng, cc='input', size_of='own')
    seen[(len(er), r[0] == r[1])] += 1
print('1. n=2, arc (0,1,1), d=2: (|E_rem|, equal labels) ->', dict(seen))

# 2. Three clusters of weak diameter 5, joined by arcs of weight 1: if they collide, Lemma 3 fails for the union
arcs = []
for i in range(3):
    x, y, z = 3 * i, 3 * i + 1, 3 * i + 2
    arcs += [(x, y, -1), (y, z, -1), (z, x, 5)]
    if i < 2:
        arcs.append((z, 3 * i + 3, 1))
n = 9
print('2. restricted:', is_restricted(n, arcs))
ge = [(u, v, max(w, 0)) for u, v, w in arcs]
D = [oracle(n, ge, [0 if v == s else None for v in range(n)], Stats()) for s in range(n)]
print('   weak diameter of each true cluster:', [max(D[a][b] for a in range(3 * i, 3 * i + 3) for b in range(3 * i, 3 * i + 3)) for i in range(3)])
print('   distance from cluster 3 back to cluster 1 in the whole graph:', D[6][0])
dist = bf(n, arcs)
print('   dist(S, last vertex) in the union S =', dist[8], 'alone in its cluster =', bf(3, [(a - 6, b - 6, w) for a, b, w in arcs if a >= 6 and b >= 6])[2])
hops = [INF] * n
for v in range(n):
    if dist[v] == 0:
        hops[v] = 0
for _ in range(n):
    for u, v, w in arcs:
        if dist[u] + w == dist[v] and hops[u] + 1 < hops[v]:
            hops[v] = hops[u] + 1
print('   arcs of the shortest path in the union:', hops[8], 'against d = 5 of Lemma 3')

# 3. Offsets 0 on x_phi
n, arcs = 2, [(0, 1, -1)]
phi = scaling(n, arcs, bf_solver, Stats())
xp = [(u, v, w + phi[u] - phi[v]) for u, v, w in scale_x(arcs, n)]
print('3. n=2, arc (0,1,-1): x_phi', xp, 'offsets 0 give', oracle(n, xp, [0, 0], Stats()), 'dist(V,.) =', bf(n, arcs))

# 4. Corollary 5 without the test of the sums: path a - b - c, one side two vertices, g = 1
m_ = Map(3, [(0, 1), (1, 2)], [[0], [1, 2], [3]])
col = {0: 0, 1: 1, 2: 0}
b = [1, -1, 1]
print('4. sum b =', sum(b), '; net outflow of f0 =', net_out(m_, route_tree(m_, b)))
dd = 4
cap = [1 if col[m_.tail(d)] == 0 else 0 for d in range(dd)]
f0 = route_tree(m_, b)
length = [cap[d] - f0[d] for d in range(dd)]
psi = a6_flow.test_dual_bf(m_, length)
print('   dual lengths', length, 'negative cycle:', psi is None, '; the darts with flow 1 from X to Y:', [(m_.tail(d), m_.head(d)) for d in range(dd) if f0[d] + (psi[m_.lft[d]] - psi[m_.rgt(d)] if psi else 0) == 1 and col[m_.tail(d)] == 0])

# 5. Orientation with sum a != m on one edge
m_ = Map(2, [(0, 1)], [[0], [1]])
a = [1, 1]
od = [1, 0]
b = [od[v] - a[v] for v in range(2)]
f0 = route_tree(m_, b)
print('5. one edge, a = (1, 1): sum b =', sum(b), 'net outflow of f0', net_out(m_, f0), 'dual lengths', [([1, 0][d] - f0[d]) for d in range(2)])

# 6. Non-restricted input: bound of the note against n(t+1)
n, arcs = 1, [(0, 0, -1)]
for t in (0, 1, 8):
    print('6. n=1, self-loop -1, t =', t, 'lemma1 gives', lemma1(n, arcs, [0], t, Stats()))
