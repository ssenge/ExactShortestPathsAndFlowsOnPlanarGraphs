"""Exhaustive checks: Lemma 5 arithmetic, Lemma 1, Lemma 3, the glitches of [2], and the scaling loop.
Every planar claim here is on n <= 4, where every digraph has a planar underlying graph. Asserted anyway."""
import itertools, os, random, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from core_check import *

ST = Counter()


def lemma5_pairs():
    """All B <= 4000: floor bound, drop. All cycles of length <= 4 with arc values in a window, for B <= 7."""
    for B in range(1, 4001):
        rho, a = phase_params(B)
        ST['l5.B'] += 1
        assert (-B) // rho + a >= -1, B
        assert rho * a < B, B
        assert rho >= 1 and a >= 0
    for B in range(1, 8):
        rho, a = phase_params(B)
        rng = range(-B, B + 7)
        for k in range(1, 5):
            for xs in itertools.product(rng, repeat=k):
                # x_phi on the cycle; cycle sum is x(C), which is >= 2|C| when w has no negative cycle
                if sum(xs) < 2 * k:
                    continue
                ST['l5.cycles'] += 1
                assert sum(x // rho + a for x in xs) >= k, (B, xs)


def lemma5_controls():
    """Each pair of the choice is needed: other pairs give a violation, so the check can fire."""
    bad = Counter()
    for B in range(1, 8):
        rho, a = phase_params(B)
        for name, (r2, a2) in {'alpha-1': (rho, a - 1), 'rho+1': (rho + 1, a)}.items():
            if a2 < 0:
                continue
            viol = False
            for k in range(1, 4):
                for xs in itertools.product(range(-B, B + 7), repeat=k):
                    if sum(xs) < 2 * k:
                        continue
                    if sum(x // r2 + a2 for x in xs) < k or min(x // r2 + a2 for x in xs) < -1:
                        viol = True
                        break
                if viol:
                    break
            bad[name] += viol
    # x without the factor 2: x(C) >= |C| only; the pair (2, 1) then fails
    v = 0
    for xs in itertools.product(range(-4, 8), repeat=2):
        if sum(xs) >= 2 and sum(x // 2 + 1 for x in xs) < 2:
            v += 1
    bad['no_factor_2'] = v
    return dict(bad)


def walks_truth(n, arcs, phi, t, maxlen):
    """Least w(P) over walks ending in v with <= t arcs negative in w_phi, by enumeration of walks. Independent of Lemma 1."""
    best = [0] * n     # empty walks
    # state: (vertex) -> DFS over walks up to maxlen
    out = [[] for _ in range(n)]
    for u, v, w in arcs:
        out[u].append((v, w, w + phi[u] - phi[v] < 0))
    for s in range(n):
        stack = [(s, 0, 0, 0)]
        while stack:
            x, wt, negs, l = stack.pop()
            if wt < best[x]:
                best[x] = wt
            if l == maxlen:
                continue
            for y, w, isn in out[x]:
                if negs + isn <= t:
                    stack.append((y, wt + w, negs + isn, l + 1))
    return best


def lemma1_exhaustive():
    """n = 3, weights -2..2 or absent on 3 chosen arcs out of 6 (all triples), phi in a small box, t = 0, 1, 2."""
    n = 3
    allarcs = [(0, 1), (1, 0), (1, 2), (2, 1), (0, 2), (2, 0)]
    ST['l1.mismatch'] = 0
    for arcset in itertools.combinations(allarcs, 4):
        for ws in itertools.product([-2, -1, 0, 2], repeat=4):
            arcs = [(a[0], a[1], w) for a, w in zip(arcset, ws)]
            for phi in itertools.product([-2, 0, 3], repeat=3):
                phi = list(phi)
                for t in (0, 1, 2):
                    d = alternate(n, arcs, phi, t)
                    # a shortest walk in the sense of the lemma has at most (t + 1)(n - 1) + t arcs: Pos parts are simple
                    tr = walks_truth(n, arcs, phi, t, (t + 1) * (n - 1) + t + 2)
                    ST['l1.cases'] += 1
                    if d != tr:
                        ST['l1.mismatch'] += 1
                    # control: t - 1 when t >= 1 must differ somewhere
                    if t >= 1:
                        d2 = alternate(n, arcs, phi, t - 1)
                        ST['l1.ctl_t_minus_differs'] += d2 != tr


def wpos_dist(n, arcs):
    a = [(u, v, max(w, 0)) for u, v, w in arcs]
    return [oracle(n, a, [0 if x == s else INF for x in range(n)]) for s in range(n)]


def is_restricted(n, arcs):
    if any(w < -1 or w > n for _, _, w in arcs):
        return False
    return bf_all(n, [(u, v, w - 1) for u, v, w in arcs]) is not None


def lemma3_case(n, arcs, S, dist0):
    """Weak diameter of S in G>=0, then shortest S-v paths in G[S], by enumeration of simple paths."""
    S = list(S)
    d = max((dist0[a][b] for a in S for b in S), default=0)
    if d >= INF:
        return
    Ss = set(S)
    inner = [a for a in arcs if a[0] in Ss and a[1] in Ss]
    out = {v: [] for v in S}
    for u, v, w in inner:
        out[u].append((v, w))
    paths = {v: [] for v in S}
    for s in S:
        stack = [(s, [s], 0, 0, 0)]
        while stack:
            x, pth, wt, wp, l = stack.pop()
            paths[x].append((wt, wp, l, tuple(pth)))
            for y, w in out[x]:
                if y not in pth:
                    stack.append((y, pth + [y], wt + w, wp + max(w, 0), l + 1))
    for v in S:
        m = min(p[0] for p in paths[v])
        for p in paths[v]:
            if p[0] == m:
                ST['l3.paths'] += 1
                if p[2] > d or p[1] > d:
                    ST['l3.FAIL'] += 1
                    print('L3 FAIL', n, arcs, S, v, p)
    # the step of [2, Lemma 3.2]: Q in G[S], the shortest v-u path inside S
    inner_d = {s: bf_from(n, inner, s) for s in S}
    for v in S:
        m = min(p[0] for p in paths[v])
        for p in paths[v]:
            if p[0] != m:
                continue
            u = p[3][0]
            q = inner_d[v][u]
            ST['g2.checked'] += 1
            if q >= INF:
                ST['g2.Q_missing'] += 1
                if 'g2.first_missing' not in EX:
                    EX['g2.first_missing'] = (n, arcs, S, v, u, d)
            elif q > d:
                ST['g2.Q_too_long'] += 1
                if 'g2.first_long' not in EX:
                    EX['g2.first_long'] = (n, arcs, S, v, u, d, q)


EX = {}


def lemma3_exhaustive():
    """All restricted digraphs on 3 vertices with weights in {absent, -1..3}, and all sets S. n = 4 with weights absent, -1, 0, 1, 4 sampled."""
    n = 3
    allarcs = list(itertools.permutations(range(n), 2))
    for ws in itertools.product([None, -1, 0, 1, 2, 3], repeat=len(allarcs)):
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        if not is_restricted(n, arcs):
            continue
        ST['l3.n3_restricted'] += 1
        D = wpos_dist(n, arcs)
        for k in (1, 2, 3):
            for S in itertools.combinations(range(n), k):
                lemma3_case(n, arcs, S, D)
    n = 4
    rng = random.Random(404)
    allarcs = list(itertools.permutations(range(n), 2))
    assert nx.check_planarity(nx.complete_graph(4))[0]
    t_end = time.time() + 120
    while time.time() < t_end:
        ws = [rng.choice([None, None, -1, -1, 0, 1, 2, 3, 4]) for _ in allarcs]
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        if not is_restricted(n, arcs):
            continue
        ST['l3.n4_restricted'] += 1
        D = wpos_dist(n, arcs)
        for k in (2, 3, 4):
            for S in itertools.combinations(range(n), k):
                lemma3_case(n, arcs, S, D)


def glitch_2_6():
    """[2, Lemma 2.6] as written, and with stay arcs. G: one arc a -> b. Layered graph built literally."""
    def layered(n, arcs, phi, t, stay):
        M = 2 * max(abs(x) for x in phi) + max(abs(w) for _, _, w in arcs)
        N = n * (t + 1) + 1
        s = N - 1
        A = []
        for u, v, w in arcs:
            wp = w + phi[u] - phi[v]
            for i in range(t + 1):
                if wp >= 0:
                    A.append((u + n * i, v + n * i, wp))
            for i in range(t):
                A.append((u + n * i, v + n * (i + 1), wp + M))
        if stay:
            for u in range(n):
                for i in range(t):
                    A.append((u + n * i, u + n * (i + 1), M))
        for u in range(n):
            A.append((s, u, -phi[u] + M))
        off = [INF] * N
        off[s] = 0
        d = oracle(N, A, off)
        return [d[v + n * t] - (t + 1) * M + phi[v] if d[v + n * t] < INF else None for v in range(n)]
    arcs = [(0, 1, 5)]
    phi = [0, 0]
    res = {'as_written_t2': layered(2, arcs, phi, 2, False), 'with_stay_t2': layered(2, arcs, phi, 2, True), 'alternation_t2': alternate(2, arcs, phi, 2)}
    # exhaustive agreement between stay-arc repair and alternation on n = 3
    n = 3
    allarcs = [(0, 1), (1, 0), (1, 2), (2, 1), (0, 2), (2, 0)]
    bad_written = 0
    bad_stay = 0
    tot = 0
    for arcset in itertools.combinations(allarcs, 3):
        for ws in itertools.product([-1, 0, 2], repeat=3):
            arcs = [(a[0], a[1], w) for a, w in zip(arcset, ws)]
            for phi in itertools.product([0, 2], repeat=3):
                phi = list(phi)
                if max(abs(x) for x in phi) == 0 and max(abs(w) for _, _, w in arcs) == 0:
                    continue
                for t in (1, 2):
                    alt = alternate(n, arcs, phi, t)
                    tot += 1
                    if layered(n, arcs, phi, t, True) != alt:
                        bad_stay += 1
                    if layered(n, arcs, phi, t, False) != alt:
                        bad_written += 1
    res['n3_cases'] = tot
    res['stay_differs_from_alternation'] = bad_stay
    res['as_written_differs'] = bad_written
    return res


def scaling_exhaustive():
    """All digraphs on 3 vertices with weights absent or -3..3: the scaling loop with Bellman-Ford as restricted solver, against Bellman-Ford."""
    n = 3
    allarcs = list(itertools.permutations(range(n), 2))
    stats = Counter()
    for ws in itertools.product([None, -3, -2, -1, 0, 1, 2, 3], repeat=len(allarcs)):
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        truth = bf_all(n, arcs)
        ST['scale.n3'] += 1
        phi = scale_potential(n, arcs, bf_solver, stats)
        if truth is None:
            ST['scale.n3_neg'] += 1
            if phi is not None:
                ST['scale.FAIL_neg_missed'] += 1
            continue
        if phi is None:
            ST['scale.FAIL_false_neg'] += 1
            continue
        for s in range(n):
            dist, par, dx = distances_from_potential(n, arcs, phi, s)
            if dist != bf_from(n, arcs, s):
                ST['scale.FAIL_dist'] += 1
            # the tree of tight arcs reaches s from every reachable vertex
            for v in range(n):
                if dist[v] < INF and v != s:
                    x = v
                    seen = 0
                    w_tot = 0
                    while x != s and seen <= n:
                        p = par[x]
                        if p is None:
                            ST['scale.FAIL_tree'] += 1
                            break
                        x = p
                        seen += 1
                    if seen > n:
                        ST['scale.FAIL_tree_cycle'] += 1
            ST['scale.dist_checked'] += n
        j = johnson_from_potential(n, arcs, phi)
        if j != truth:
            ST['scale.FAIL_johnson'] += 1
        if any(w + j[u] - j[v] < 0 for u, v, w in arcs):
            ST['scale.FAIL_johnson_pot'] += 1
    ST['scale.phases'] = stats['phases']
    ST['scale.max_B'] = stats['max_B']


if __name__ == '__main__':
    import os, signal
    def _alarm(*_):
        print('ALARM partial', sys.argv[1:], {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    which = sys.argv[1]
    if which == 'arith':
        lemma5_pairs()
        print('controls', lemma5_controls())
        print('glitch_2_6', glitch_2_6())
    elif which == 'l1':
        lemma1_exhaustive()
    elif which == 'l3':
        lemma3_exhaustive()
        print('examples', EX)
    elif which == 'scale':
        scaling_exhaustive()
    print({k: ST[k] for k in sorted(ST)})
    print({k: STAT[k] for k in sorted(STAT)})
