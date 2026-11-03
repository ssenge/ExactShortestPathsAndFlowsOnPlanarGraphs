"""Theorem 1 on the whole stack, all small digraphs and targeted planar ones; Corollary 6; negative controls for the flow reduction.

  a7_stack.py exh <nmax> <seed>          every digraph with few arcs: loops, parallels, antiparallels, zero cycles; whole stack, truth Bellman-Ford
  a7_stack.py rand <seed> <secs>         random and targeted instances up to n = 40
  a7_stack.py mean <seed> <secs>         Corollary 6 against enumeration of simple cycles, incl. acyclic graphs
  a7_stack.py ctl <seed>                 controls that must fire
"""
import collections
import fractions
import itertools
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
import a6_flow
import networkx as nx


def one(n, arcs, rng, c, R=3, t=8, cc=1.0, label='tarjan', tag=''):
    truth = bf(n, arcs)
    st = Stats()

    def solver(nn, kept):
        return restricted(nn, kept, R=R, t=t, c=cc, rng=rng, st=st, label=label)
    phi = scaling(n, arcs, solver, st)
    c[tag + 'runs'] += 1
    c[tag + 'max_oracle'] = max(c[tag + 'max_oracle'], st['oracle'])
    c[tag + 'max_w_fed'] = max(c[tag + 'max_w_fed'], st['max_w'])
    c[tag + 'max_off_fed'] = max(c[tag + 'max_off_fed'], st['max_off'])
    if truth is None:
        c[tag + 'neg'] += 1
        if phi is not None:
            c[tag + 'FAIL.neg_missed'] += 1
            print('NEG MISSED', n, arcs)
        return
    if phi is None:
        c[tag + 'false_report'] += 1
        print('FALSE REPORT', n, arcs, 'R', R, 't', t, 'c', cc, flush=True)
        return
    xa = scale_x(arcs, n)
    if any(w + phi[u] - phi[v] < 0 for u, v, w in xa):
        c[tag + 'FAIL.pot'] += 1
    s = rng.randrange(n)
    init = [INF] * n
    init[s] = 0
    if dist_from_phi(n, arcs, s, phi, st) != bf(n, arcs, init):
        c[tag + 'FAIL.dist'] += 1
        print('DIST', n, arcs, s)
    c[tag + 'dist'] += n


def exh(nmax, seed):
    rng = random.Random(seed)
    c = collections.Counter()
    t0 = time.time()
    for n in range(1, nmax + 1):
        cand = [(u, v, w) for u in range(n) for v in range(n) for w in (-2, -1, 0, 1, 2)]
        for k in range(0, 4 if n >= 3 else 5):
            for arcs in itertools.combinations_with_replacement(cand, k):
                one(n, list(arcs), rng, c)
    print('exh', json.dumps(dict(sorted(c.items()))), 'secs', round(time.time() - t0))


def planar_arcs(rng, nmax):
    k = rng.randrange(4)
    if k == 0:
        a, b = rng.randrange(2, 7), rng.randrange(2, 7)
        n = a * b
        net = []
        for i in range(a):
            for j in range(b):
                x = i * b + j
                if j + 1 < b:
                    net.append((x, x + 1))
                if i + 1 < a:
                    net.append((x, x + b))
    elif k == 1:
        n = rng.randrange(3, nmax)
        net = [(i, i + 1) for i in range(n - 1)]
    elif k == 2:
        n = rng.randrange(4, nmax)
        net = [(0, i) for i in range(1, n)] + [(i, i + 1) for i in range(1, n - 1)] + [(1, n - 1)]
    else:
        n = rng.randrange(3, nmax)
        net = [(i, (i + 1) % n) for i in range(n)]
    return n, net


def targeted(rng, nmax):
    n, net = planar_arcs(rng, nmax)
    W = rng.choice([1, 2, 5, n, n * n, n ** 3, 10 ** 6])
    style = rng.randrange(6)
    p = [rng.randrange(-W, W + 1) for _ in range(n)]
    arcs = []
    if style == 0:      # all tight: zero cycles everywhere
        for x, y in net:
            arcs += [(x, y, p[x] - p[y]), (y, x, p[y] - p[x])]
    elif style == 1:    # all tight, one arc one less: a negative cycle of weight -1 exactly
        for x, y in net:
            arcs += [(x, y, p[x] - p[y]), (y, x, p[y] - p[x])]
        i = rng.randrange(len(arcs))
        arcs[i] = (arcs[i][0], arcs[i][1], arcs[i][2] - 1)
    elif style == 2:    # the most negative no-cycle graph: long directed path of -W with heavy returns
        for x, y in net:
            arcs.append((x, y, -W))
            arcs.append((y, x, W + rng.choice([0, 0, 1])))
    elif style == 3:    # weight -W on one direction and exactly enough on the other, mixed with parallels
        for x, y in net:
            arcs.append((x, y, -W))
            arcs.append((y, x, W))
            if rng.random() < 0.3:
                arcs.append((x, y, -W + rng.randrange(0, 3)))
    elif style == 4:    # one-way, acyclic or nearly
        order = list(range(n))
        rng.shuffle(order)
        pos = {v: i for i, v in enumerate(order)}
        for x, y in net:
            u, v = (x, y) if pos[x] < pos[y] else (y, x)
            arcs.append((u, v, rng.randrange(-W, W + 1)))
    else:               # self-loops of weight 0 and positive, and sometimes negative
        for x, y in net:
            arcs += [(x, y, rng.randrange(-1, 3)), (y, x, rng.randrange(0, 3))]
        for v in range(n):
            if rng.random() < 0.2:
                arcs.append((v, v, rng.choice([0, 1, 5, 0, 0, -1])))
    return n, arcs


def rand_stack(seed, secs):
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        n, arcs = targeted(rng, 30)
        if len(arcs) > 100:
            continue
        one(n, arcs, rng, c)
    print('rand', json.dumps(dict(sorted(c.items()))))


def simple_cycle_means(n, arcs):
    best = {}
    for u, v, w in arcs:
        if (u, v) not in best or w < best[u, v]:
            best[u, v] = w
    g = nx.DiGraph()
    g.add_nodes_from(range(n))
    for (u, v), w in best.items():
        g.add_edge(u, v, weight=w)
    res = None
    for cyc in nx.simple_cycles(g):
        tot = sum(best[cyc[i], cyc[(i + 1) % len(cyc)]] for i in range(len(cyc)))
        m = fractions.Fraction(tot, len(cyc))
        if res is None or m < res:
            res = m
    return res


def mean_by_tests(n, arcs, tester):
    """Corollary 6 as written: binary search on p/q with a negative cycle test on q w - p."""
    W = max([abs(w) for u, v, w in arcs] + [0])
    lo = fractions.Fraction(-W - 1)
    hi = fractions.Fraction(W + 1)
    tests = 0

    def neg_below(x):
        nonlocal tests
        tests += 1
        p, q = x.numerator, x.denominator
        return tester(n, [(u, v, q * w - p) for u, v, w in arcs])
    # invariant: mean >= lo and mean < hi, or no cycle at all
    width = fractions.Fraction(1, n * n + 1)
    while hi - lo >= width:
        mid = (lo + hi) / 2
        if neg_below(mid):
            hi = mid
        else:
            lo = mid
    # one fraction with denominator <= n in [lo, hi)
    cands = []
    for q in range(1, n + 1):
        p = (lo * q).__ceil__()
        if fractions.Fraction(p, q) < hi:
            cands.append(fractions.Fraction(p, q))
    return sorted(set(cands)), tests


def mean(seed, secs):
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    ex = None

    def tester_bf(n, a):
        return has_neg_cycle(n, a)

    def tester_stack(n, a):
        return scaling(n, a, lambda nn, kept: restricted(nn, kept, R=2, t=8, c=1.0, rng=rng, st=Stats()), Stats()) is None
    while time.time() < end:
        n = rng.randrange(1, 7)
        m = rng.randrange(0, 2 * n + 2)
        W = rng.choice([1, 3, 10, 100])
        arcs = [(rng.randrange(n), rng.randrange(n), rng.randrange(-W, W + 1)) for _ in range(m)]
        if rng.random() < 0.3:    # acyclic
            arcs = [(min(a, b), max(a, b), w) for a, b, w in arcs if a != b]
        tr = simple_cycle_means(n, arcs)
        use_stack = rng.random() < 0.05 and n <= 5
        cands, tests = mean_by_tests(n, arcs, tester_stack if use_stack else tester_bf)
        c['runs'] += 1
        c['runs_stack'] += use_stack
        c['max_tests'] = max(c['max_tests'], tests)
        if len(cands) > 1:
            c['FAIL.two_candidates'] += 1
        if tr is None:
            c['acyclic'] += 1
            if cands:
                c['acyclic_but_answer_fraction'] += 1
                ex = ex or (n, arcs, [str(x) for x in cands])
            continue
        if cands != [tr]:
            c['FAIL.mean'] += 1
            print('MEAN', n, arcs, tr, cands)
    print('mean', json.dumps(dict(sorted(c.items()))), 'acyclic example', ex)


def ctl(seed):
    """The checkers must fire when the logic is damaged."""
    rng = random.Random(seed)
    res = collections.Counter()
    # flow: sign of the dual arc reversed, or potentials dropped
    for _ in range(400):
        m_ = a6_flow.random_plane_map(rng, 7)
        dd = 2 * len(m_.edges)
        cap = [rng.randrange(0, 4) for _ in range(dd)]
        s, t = rng.sample(range(m_.n), 2)
        true = a6_flow.nx_value(m_.n, m_.edges, cap, s, t)

        def good(length):
            return a6_flow.test_dual_bf(m_, length)

        def wrong_dir(length):
            # dual dart from lft to rgt: the sign error a careless reduction makes
            return bf(m_.nf, [(m_.lft[d], m_.rgt(d), length[d]) for d in range(dd)])

        def no_neg_detect(length):
            # ignores negative arcs on the face cycle: test by dropping loops (bridges)
            return bf(m_.nf, [(m_.rgt(d), m_.lft[d], length[d]) for d in range(dd) if m_.rgt(d) != m_.lft[d]])
        c = collections.Counter()
        try:
            v1, f1 = a6_flow.theorem2(m_, cap, s, t, good, c)
            res['good_wrong'] += (v1 != true) or not a6_flow.check_flow(m_, cap, f1, v1, s, t, c)
        except AssertionError:
            res['good_assert'] += 1
        for name, tst in (('wrong_dir', wrong_dir), ('no_loops', no_neg_detect)):
            c = collections.Counter()
            try:
                v2, f2 = a6_flow.theorem2(m_, cap, s, t, tst, c)
                res[name + '_fires'] += (v2 != true) or not a6_flow.check_flow(m_, cap, f2, v2, s, t, c)
            except (AssertionError, TypeError):
                res[name + '_fires'] += 1
            res[name + '_runs'] += 1
    # Theorem 1: the restricted solver replaced by the zero potential, by a damaged index shift
    for _ in range(300):
        n, arcs = targeted(rng, 12)
        if bf(n, arcs) is None:
            continue
        res['t1_runs'] += 1
        if scaling(n, arcs, lambda nn, kept: [0] * nn, Stats()) is None:
            res['t1_zero_solver_reports'] += 1

        def noshift(nn, kept):
            if not kept:
                return [0] * nn
            return restricted(nn, kept, R=1, t=0, c=1.0, rng=rng, st=Stats())
        if scaling(n, arcs, noshift, Stats()) is None:
            res['t1_t0_R1_reports'] += 1
    print('ctl', json.dumps(dict(sorted(res.items()))))


if __name__ == '__main__':
    p = sys.argv[1]
    if p == 'exh':
        exh(int(sys.argv[2]), int(sys.argv[3]))
    elif p == 'rand':
        rand_stack(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'mean':
        mean(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'ctl':
        ctl(int(sys.argv[2]))
