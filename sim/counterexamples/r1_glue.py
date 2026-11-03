"""Lemma R1: random pieces A_i, emulators B_i with dist_A <= dist_B <= lam*dist_A on T_i,
random equivalence ~ on the disjoint union of terminals (incl. classes inside one piece),
zero weights and unreachable pairs allowed.  Check the claim on all terminal images."""
import numpy as np, networkx as nx, math
rng = np.random.default_rng(5)
fails = 0; checks = 0
for trial in range(400):
    k = int(rng.integers(1, 5)); lam = 1 + rng.random()
    A, B, Ts = [], [], []
    for i in range(k):
        n = int(rng.integers(2, 9))
        G = nx.gnp_random_graph(n, rng.random() * 0.6 + 0.1, seed=int(rng.integers(1e9)), directed=True)
        Ai = nx.DiGraph()
        Ai.add_nodes_from((i, v) for v in G)
        for a, b in G.edges():
            Ai.add_edge((i, a), (i, b), weight=int(rng.integers(0, 6)))
        T = [(i, v) for v in G if rng.random() < 0.6] or [(i, 0)]
        sp = dict(nx.all_pairs_dijkstra_path_length(Ai))
        Bi = nx.DiGraph(); Bi.add_nodes_from(T)
        Bi.add_node((i, 'steiner'))
        for a in T:
            for b in T:
                if a != b and b in sp[a]:
                    Bi.add_edge(a, b, weight=sp[a][b] * (1 + rng.random() * (lam - 1)))
        A.append(Ai); B.append(Bi); Ts.append(T)
    allT = [t for T in Ts for t in T]
    lab = {t: int(rng.integers(0, max(1, len(allT) * 2 // 3))) for t in allT}   # class id
    def glue(pieces):
        H = nx.MultiDiGraph()
        f = lambda v: ('cls', lab[v]) if v in lab else v
        for Pc in pieces:
            H.add_nodes_from(f(v) for v in Pc)
            for a, b, d in Pc.edges(data=True):
                H.add_edge(f(a), f(b), weight=d['weight'])
        return H
    GA, GB = glue(A), glue(B)
    imgs = sorted(set(('cls', c) for c in lab.values()))
    dA = dict(nx.all_pairs_dijkstra_path_length(GA)); dB = dict(nx.all_pairs_dijkstra_path_length(GB))
    for x in imgs:
        for y in imgs:
            a = dA[x].get(y, math.inf); b = dB[x].get(y, math.inf)
            checks += 1
            if not (a <= b + 1e-9 and (b <= lam * a + 1e-9 or (a == math.inf and b == math.inf))):
                fails += 1
print('R1: %d terminal-image pairs checked, %d failures' % (checks, fails))
