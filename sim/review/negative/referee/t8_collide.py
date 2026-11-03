"""Algorithm 3 of [3] with Section 5.2: how likely are equal labels on different strong components, as n grows? [3] says w.h.p. distinct, by a first moment.
For each run the expected number of colliding pairs is computed exactly from the intervals of the base cases (Rao-Blackwell), so few runs suffice.
Prediction: about const/n with N^2 dilation (so not n^-c for every c), far smaller with N^4; with 'own' n, singletons collide with certainty."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from t4_ldd import Topsort


def grid(a):
    n = a * a
    E = []
    for i in range(a):
        for j in range(a):
            x = i * a + j
            if j + 1 < a:
                E.append((x, x + 1))
            if i + 1 < a:
                E.append((x, x + a))
    assert nx.check_planarity(nx.Graph(E))[0]
    return n, E


def expected_collisions(bases):
    tot = 0.0
    for i, (a, b) in enumerate(bases):
        for c, d in bases[i + 1:]:
            ov = min(b, d) - max(a, c) + 1
            if ov > 0:
                tot += ov / ((b - a + 1) * (d - c + 1))
    return tot


if __name__ == '__main__':
    runs = int(sys.argv[1])
    rng = random.Random(3)
    for keep_p in (0.0, 0.3):
        for cc_n, conn, dil in (('parent', 'network', 2), ('parent', 'arcs', 2), ('parent', 'network', 4), ('own', 'arcs', 2), ('own', 'network', 2)):
            row = []
            for a in (4, 6, 8, 12):
                n, E = grid(a)
                s = 0.0
                for _ in range(runs):
                    arcs = []
                    for x, y in E:
                        if rng.random() < keep_p:
                            arcs.append((x, y) if rng.random() < 0.5 else (y, x))
                    net = E if conn == 'network' else arcs
                    T = Topsort(n, arcs, dil=dil, cc_n=cc_n, net=net)
                    T.run(rng)
                    s += expected_collisions(T.bases)
                row.append((n, round(s / runs, 7), round(s / runs * n, 4)))
            print('keep', keep_p, cc_n, conn, 'dil', dil, '(n, E collisions, n*E):', row, flush=True)
