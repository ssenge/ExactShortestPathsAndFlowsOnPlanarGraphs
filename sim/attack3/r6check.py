"""Lemma 15' step 4 / Lemma R6 / (I3) in exact arithmetic: eta_X = 1/ceil(max|V(K_C)|/eps'), cap at m,
round up to multiples of eta; check d_K <= d_Khat <= (1+eps') d_K on terminals, weights multiples of eta,
1/eta integer, integer outside-edge weights multiples of eta."""
import random, math, itertools, sys
from fractions import Fraction as F
import networkx as nx

def apsp(n, arcs):
    INF = None
    d = [[None]*n for _ in range(n)]
    for i in range(n): d[i][i] = F(0)
    for (a, b), w in arcs.items():
        if d[a][b] is None or w < d[a][b]: d[a][b] = w
    for k in range(n):
        for i in range(n):
            if d[i][k] is None: continue
            for j in range(n):
                if d[k][j] is None: continue
                v = d[i][k] + d[k][j]
                if d[i][j] is None or v < d[i][j]: d[i][j] = v
    return d

rng = random.Random(1); bad = 0; checks = 0; worst = 0
for it in range(int(sys.argv[1]) if len(sys.argv) > 1 else 300):
    eps = F(1, rng.choice([1, 2, 3, 5, 10, 17]))
    Ks = []
    for c in range(rng.randint(1, 4)):
        n = rng.randint(3, 14); T = list(range(rng.randint(2, n)))
        G = nx.gnp_random_graph(n, 0.35, seed=rng.randint(0, 10**9))
        while not nx.is_connected(G):
            a, b = rng.sample(range(n), 2); G.add_edge(a, b)
        arcs = {}
        for a, b in G.edges():
            arcs[(a, b)] = F(rng.randint(0, 40), rng.randint(1, 9)); arcs[(b, a)] = F(rng.randint(0, 40), rng.randint(1, 9))
        d = apsp(n, arcs)
        mn = min(d[a][b] for a in T for b in T if a != b)
        if mn == 0: continue
        s = 1 / mn                                     # scale so that d_K >= 1 on terminals (as in step 4)
        arcs = {k: v * s for k, v in arcs.items()}
        Ks.append((n, T, arcs))
    if not Ks: continue
    eta = F(1, math.ceil(F(max(n for n, _, _ in Ks)) / eps))
    assert (1 / eta).denominator == 1
    for n, T, arcs in Ks:
        d = apsp(n, arcs)
        m = max(d[a][b] for a in T for b in T if a != b)
        hat = {}
        for k, w in arcs.items():
            w2 = min(w, m); hat[k] = math.ceil(w2 / eta) * eta
            assert (hat[k] / eta).denominator == 1 and hat[k] <= m + eta
        dh = apsp(n, hat)
        for a in T:
            for b in T:
                if a == b: continue
                checks += 1
                r = dh[a][b] / d[a][b]
                worst = max(worst, (r - 1) / eps)
                if not (d[a][b] <= dh[a][b] <= (1 + eps) * d[a][b]): bad += 1
    W = rng.randint(1, 10**6)                          # integer outside-edge weight
    assert (F(W) / eta).denominator == 1
print('R6/(I3) exact checks', checks, 'violations', bad, 'worst (ratio-1)/eps', float(worst))
