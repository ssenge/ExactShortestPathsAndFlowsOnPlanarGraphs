"""A suggestion to the author, tested: the 'negative cycle' side of Theorem 1 can be certified with the note's own tools.
By Corollary 6 find the min mean p/q. If p/q < 0: Theorem 1 on q*w - p gives integer potentials with nonnegative reduced weights (certified locally).
Every cycle of mean p/q is then tight, and every tight cycle has mean p/q. Strong components of the tight arcs ([3, Cor. 33]) show one:
a vertex in a nontrivial component points to a tight out-neighbour in it; the pointers reach a cycle, of weight p/q * length < 0.
Checked on all digraphs with 3 vertices and small weights, and on random planar digraphs. Controls: at p/q above the min mean the test sees a negative
cycle; at p/q just below it no tight cycle exists."""
import itertools, os, random, sys
from collections import Counter
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from core_check import *
from t2_prop4 import planar_random
from t3_flow import cor6, min_mean_truth

ST = Counter()


def certificate(n, arcs, mu):
    p, q = mu.numerator, mu.denominator
    w2 = [(u, v, q * w - p) for u, v, w in arcs]
    phi = scale_potential(n, w2, bf_solver)
    if phi is None:
        return 'neg'
    psi = johnson_from_potential(n, w2, phi)
    assert all(w + psi[u] - psi[v] >= 0 for u, v, w in w2)
    tight = [(u, v) for u, v, w in w2 if w + psi[u] - psi[v] == 0]
    comp = tarjan(n, tight)
    ptr = {}
    for u, v in tight:
        if comp[u] == comp[v]:
            ptr.setdefault(u, v)
    if not ptr:
        return None
    # follow the pointers from any vertex in a nontrivial component
    x = next(iter(ptr))
    seen = {}
    path = []
    while x not in seen:
        seen[x] = len(path)
        path.append(x)
        x = ptr[x]
    cyc = path[seen[x]:]
    wt = {}
    for u, v, w in arcs:
        wt[(u, v)] = min(w, wt.get((u, v), INF))
    tot = sum(wt[(cyc[i], cyc[(i + 1) % len(cyc)])] for i in range(len(cyc)))
    return Fraction(tot, len(cyc)), cyc


def run(n, arcs):
    tr = min_mean_truth(n, arcs)
    W = max(abs(w) for _, _, w in arcs)
    mu, _ = cor6(n, arcs, W, bf_solver)
    ST['runs'] += 1
    if mu != tr:
        ST['FAIL.mean'] += 1
        return
    if tr is None:
        ST['acyclic'] += 1
        return
    ST['neg_cycle' if tr < 0 else 'no_neg'] += 1
    c = certificate(n, arcs, tr)
    if c == 'neg' or c is None or c[0] != tr:
        ST['FAIL.certificate'] += 1
        return
    # controls
    above = tr + Fraction(1, 2 * n * n)
    if certificate(n, arcs, above) != 'neg':
        ST['FAIL.ctl_above'] += 1
    below = tr - Fraction(1, 2 * n * n)
    if certificate(n, arcs, below) is not None:
        ST['FAIL.ctl_below'] += 1
    ST['ctl_ok'] += 1


if __name__ == '__main__':
    import signal
    def _alarm(*_):
        print('ALARM partial', {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    n = 3
    allarcs = list(itertools.permutations(range(n), 2))
    for ws in itertools.product([None, -2, -1, 0, 1, 2], repeat=len(allarcs)):
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        if arcs:
            run(n, arcs)
    rng = random.Random(9)
    for _ in range(int(sys.argv[1])):
        n, E = planar_random(rng, 9)
        W = rng.choice([1, 3, 10])
        arcs = []
        for a, b in E:
            if rng.random() < 0.6:
                arcs.append((a, b, rng.randrange(-W, 2 * W + 1)))
            if rng.random() < 0.6:
                arcs.append((b, a, rng.randrange(-W, 2 * W + 1)))
        if arcs:
            run(n, arcs)
    print({k: ST[k] for k in sorted(ST)})
