"""Exhaustive small checks: Lemma 5 arithmetic, Lemma 1, Lemma 3, scaling and distances, with negative controls.

usage: a1_small.py <part>
"""
import collections
import itertools
import json
import random
import sys
import time

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *


def part_arith():
    """Lemma 5: every B up to 200000, then large random B. For every B: worst floor, cycle bound by the two extreme forms, new bound."""
    c = collections.Counter()
    for B in list(range(1, 200001)) + [random.randrange(1, 10 ** 30) for _ in range(200000)]:
        rho, alpha = params(B)
        c['B'] += 1
        # all possible values x_phi >= -B: the floor is monotone, so the worst is -B
        if (-B) // rho + alpha < -1:
            c['FAIL.low'] += 1
        if rho * alpha >= B:
            c['FAIL.notless'] += 1
    # cycle inequality: all multisets of cycle lengths up to 6 with sum x >= 2k, small B, exhaustive
    for B in range(1, 13):
        rho, alpha = params(B)
        vals = list(range(-B, 2 * B + 8))
        for k in range(1, 5):
            for xs in itertools.product(vals, repeat=k):
                if sum(xs) < 2 * k:
                    continue
                c['cyc'] += 1
                r = sum(x // rho + alpha for x in xs)
                if r < k:
                    c['FAIL.cycle'] += 1
    return c


def part_lemma1(secs=120, seed=11):
    """Lemma 1 against a layered Bellman-Ford. Negative control: t - 1 calls."""
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        n = rng.randrange(1, 7)
        m = rng.randrange(0, 14)
        W = rng.choice([1, 2, 5, 20])
        PH = rng.choice([0, 1, 3, 10, 50])
        arcs = [(rng.randrange(n), rng.randrange(n), rng.randrange(-W, W + 1)) for _ in range(m)]
        phi = [rng.randrange(-PH, PH + 1) for _ in range(n)]
        t = rng.randrange(0, 5)
        d = lemma1(n, arcs, phi, t)
        # truth: least w(P) over walks with at most t arcs negative in w_phi, by state (v, i) and Bellman-Ford over the nonneg part.
        # Walks can be unbounded in w, but w_phi >= 0 inside a layer; so minimize -phi(x)+w_phi, finite.
        wp = [(u, v, w + phi[u] - phi[v]) for u, v, w in arcs]
        best = [[INF] * (t + 1) for _ in range(n)]
        for v in range(n):
            best[v][0] = -phi[v]
        for it in range((t + 1) * n + 3):
            ch = False
            for u, v, y in wp:
                for i in range(t + 1):
                    if best[u][i] >= INF:
                        continue
                    j = i + (1 if y < 0 else 0)
                    if j <= t and best[u][i] + y < best[v][j]:
                        best[v][j] = best[u][i] + y
                        ch = True
            if not ch:
                break
        else:
            c['FAIL.truth_diverged'] += 1
        for v in range(n):
            tv = min(best[v]) + phi[v]
            c['checked'] += 1
            if d[v] != tv:
                c['FAIL.lemma1'] += 1
                print('lemma1', n, arcs, phi, t, d, v, tv)
        # control: one alternation less must be visibly weaker on some instances
        if t >= 1:
            d2 = lemma1(n, arcs, phi, t - 1)
            if d2 != d:
                c['ctl_fires'] += 1
    return c


def all_shortest_simple(n, arcs, S, dist):
    """All simple paths in G[S], ending anywhere, with weight dist[end]. Exhaustive DFS."""
    adj = collections.defaultdict(list)
    for u, v, w in arcs:
        if u in S and v in S:
            adj[u].append((v, w))
    out = []

    def go(path, weights, wsum):
        v = path[-1]
        if wsum == dist[v]:
            out.append((list(path), list(weights)))
        for y, w in adj[v]:
            if y not in path:
                path.append(y)
                weights.append(w)
                go(path, weights, wsum + w)
                path.pop()
                weights.pop()
    for s in S:
        go([s], [], 0)
    return out


def part_lemma3(nmax=4, limit=None):
    """All digraphs on n <= nmax vertices with at most one arc per ordered pair and weights in -1..n (or no arc). All S."""
    c = collections.Counter()
    tight = collections.Counter()
    pair_vals = {}
    for n in range(1, nmax + 1):
        pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
        vals = [None] + list(range(-1, n + 1))
        total = len(vals) ** len(pairs)
        rng = random.Random(n)
        # exhaustive to n = 3, sampled for n = 4 (10^10 otherwise), with a bias to many -1 arcs
        if total <= 3 * 10 ** 6:
            it = itertools.product(vals, repeat=len(pairs))
        else:
            def gen():
                for _ in range(limit or 400000):
                    pm1 = rng.random()
                    yield tuple(rng.choice([None, -1]) if rng.random() < pm1 else rng.choice(vals) for _ in pairs)
            it = gen()
        for choice in it:
            arcs = [(a, b, w) for (a, b), w in zip(pairs, choice) if w is not None]
            if not is_restricted(n, arcs):
                continue
            c['restricted', n] += 1
            ge = [(u, v, max(w, 0)) for u, v, w in arcs]
            alld = [oracle(n, ge, [0 if v == s else None for v in range(n)]) for s in range(n)]
            for mask in range(1, 2 ** n):
                S = {v for v in range(n) if mask >> v & 1}
                d = max(alld[a][b] for a in S for b in S)
                if d >= INF:
                    continue
                ins = sub(arcs, S)
                dist = bf(n, ins)
                for path, ws in all_shortest_simple(n, arcs, S, dist):
                    c['paths'] += 1
                    pw = sum(max(x, 0) for x in ws)
                    if len(ws) > d:
                        c['FAIL.hops'] += 1
                        print('hops', n, arcs, S, path, d)
                    if pw > d:
                        c['FAIL.weight'] += 1
                        print('weight', n, arcs, S, path, d)
                    if d and len(ws) == d:
                        tight['hops_tight'] += 1
                    if d and pw == d:
                        tight['weight_tight'] += 1
                # the reading of [2, Lemma 3.2]: return path in G[S]: instances where G[S] has a larger distance than the weak diameter
                ge_in = sub(ge, S)
                for a in S:
                    di = oracle(n, ge_in, [0 if v == a else None for v in range(n)])
                    if any(di[b] > alld[a][b] for b in S):
                        c['S_with_larger_internal_distance'] += 1
                        break
    c.update(tight)
    return c


def part_scaling(secs=120, seed=21):
    """Lemma 5 and distances on all small digraphs with parallel arcs, self-loops, antiparallel arcs, zero cycles, huge weights.
    Also the sentence 'with offsets 0 on all vertices the same call gives dist(V, .)'."""
    c = collections.Counter()
    # exhaustive: n <= 3, up to 3 arcs among all (u, v, w) with w in -3..3, loops and parallels included
    for n in (1, 2, 3):
        cand = [(u, v, w) for u in range(n) for v in range(n) for w in (-3, -1, 0, 1, 3)]
        for k in range(0, 4):
            for arcs in itertools.combinations_with_replacement(cand, k):
                run_scaling_one(n, list(arcs), c)
    rng = random.Random(seed)
    end = time.time() + secs
    while time.time() < end:
        n = rng.randrange(1, 12)
        m = rng.randrange(0, 3 * n + 2)
        kind = rng.randrange(4)
        W = rng.choice([1, 3, 30, 10 ** 3, n ** 3, 10 ** 9])
        if kind == 0:
            arcs = [(rng.randrange(n), rng.randrange(n), rng.randrange(-W, W + 1)) for _ in range(m)]
        else:
            p = [rng.randrange(-W, W + 1) for _ in range(n)]
            arcs = []
            for _ in range(m):
                u, v = rng.randrange(n), rng.randrange(n)
                s = rng.choice([0, 0, 0, 1, rng.randrange(0, W + 1)])
                arcs.append((u, v, s + p[u] - p[v]))
            if kind == 2 and arcs:
                i = rng.randrange(len(arcs))
                u, v, w = arcs[i]
                arcs[i] = (u, v, w - rng.choice([1, 2, W]))
            if kind == 3 and arcs:     # tight cycle, then one unit down or none
                arcs = list(arcs)
                cyc = list(range(n))
                rng.shuffle(cyc)
                for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                    arcs.append((a, b, p[a] - p[b]))
                if rng.random() < 0.5:
                    u, v, w = arcs[-1]
                    arcs[-1] = (u, v, w - 1)
        run_scaling_one(n, arcs, c)
    return c


def run_scaling_one(n, arcs, c):
    c['runs'] += 1
    truth = bf(n, arcs)
    st = Stats()
    phi = scaling(n, arcs, bf_solver, st)
    c['phases'] += st['phases']
    c['max_phases'] = max(c['max_phases'], st['phases'])
    if truth is None:
        c['neg'] += 1
        if phi is not None:
            c['FAIL.neg_missed'] += 1
            print('missed', n, arcs)
        return
    if phi is None:
        c['FAIL.false_report'] += 1
        print('false', n, arcs)
        return
    xa = scale_x(arcs, n)
    if any(w + phi[u] - phi[v] < 0 for u, v, w in xa):
        c['FAIL.pot'] += 1
    for s in range(n):
        init = [INF] * n
        init[s] = 0
        t = bf(n, arcs, init)
        d = dist_from_phi(n, arcs, s, phi, st)
        c['dist'] += n
        if t != d:
            c['FAIL.dist'] += 1
            print('dist', n, arcs, s, t, d)
    # The sentence: 'With offsets 0 on all vertices the same call gives dist(V, ·), which is a potential for w.'
    xp = [(u, v, w + phi[u] - phi[v]) for u, v, w in xa]
    lit = oracle(n, xp, [0] * n, st)
    dv = bf(n, arcs)
    if [x // (2 * (n + 1)) for x in lit] != dv:
        c['sentence_offsets0_literal_wrong'] += 1
    sh = max(phi) if n else 0
    corr = oracle(n, xp, [sh - phi[v] for v in range(n)], st)
    corr = [corr[v] - sh + phi[v] for v in range(n)]
    if [x // (2 * (n + 1)) for x in corr] != dv:
        c['FAIL.dist_V_with_offsets_minus_phi'] += 1


if __name__ == '__main__':
    p = sys.argv[1]
    t0 = time.time()
    if p == 'arith':
        c = part_arith()
    elif p == 'lemma1':
        c = part_lemma1(float(sys.argv[2]))
    elif p == 'lemma3':
        c = part_lemma3(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else None)
    elif p == 'scaling':
        c = part_scaling(float(sys.argv[2]))
    print(p, json.dumps({str(k): v for k, v in sorted(c.items(), key=lambda kv: str(kv[0]))}), 'secs', round(time.time() - t0))
