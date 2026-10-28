"""Lemma R6: cap at m = max terminal distance, round up to multiples of eta, eta*|V| <= eps.
Random strongly connected digraphs with real weights (incl. 0 and huge), terminal distances
scaled so that min terminal distance is exactly 1 (worst case for the additive error)."""
import numpy as np, networkx as nx, math
rng = np.random.default_rng(9)
fails = 0; checks = 0; worst = 0
for t in range(500):
    n = int(rng.integers(3, 25))
    G = nx.DiGraph()
    for v in range(n):
        G.add_edge(v, (v + 1) % n); G.add_edge((v + 1) % n, v)
    for _ in range(int(rng.integers(0, 3 * n))):
        a, b = rng.integers(0, n, 2)
        if a != b: G.add_edge(int(a), int(b))
    for a, b in G.edges():
        r = rng.random()
        G[a][b]['weight'] = 0.0 if r < 0.15 else (1e6 * rng.random() if r < 0.2 else rng.random() * 10)
    T = sorted(set(int(x) for x in rng.choice(n, int(rng.integers(2, n + 1)), replace=False)))
    sp = dict(nx.all_pairs_dijkstra_path_length(G))
    dmin = min(sp[a][b] for a in T for b in T if a != b)
    if dmin == 0: continue
    for a, b in G.edges(): G[a][b]['weight'] /= dmin       # now min terminal distance = 1
    sp = dict(nx.all_pairs_dijkstra_path_length(G))
    m = max(sp[a][b] for a in T for b in T if a != b)
    eps = rng.choice([0.5, 0.1, 0.01]); eta = eps / n
    H = G.copy()
    for a, b in H.edges():
        w = min(H[a][b]['weight'], m)
        H[a][b]['weight'] = math.ceil(w / eta - 1e-12) * eta
    sq = dict(nx.all_pairs_dijkstra_path_length(H))
    for a in T:
        for b in T:
            if a == b: continue
            checks += 1
            ok = sp[a][b] - 1e-9 <= sq[a][b] <= (1 + eps) * sp[a][b] + 1e-9
            fails += not ok
            worst = max(worst, (sq[a][b] / sp[a][b] - 1) / eps)
print('R6: %d pairs, %d failures, worst (ratio-1)/eps = %.3f' % (checks, fails, worst))
