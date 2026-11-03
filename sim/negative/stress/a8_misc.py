"""Remaining targeted checks.

  a8_misc.py ghat <seed> <secs>    planarity, number of nodes and hop diameter of the face-disjoint graph on random multigraph maps
  a8_misc.py depth                 recursion depth of Algorithm 3 of [3] on worst-case digraphs, against log2 n
  a8_misc.py merge <seed> <secs>   the merging of disjoint calls by a large weight: which M keeps the answers, for Lemma 1 and for balls
  a8_misc.py verify <seed> <secs>  the sentence 'an answer with distances is always right': a wrong oracle answer with all stated checks passing
  a8_misc.py small3                [3, Cor. 27] sampling: instances smaller than the sample size; smallest collision instances printed in full
"""
import collections
import json
import math
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
import a6_flow
import networkx as nx


def hop_diam(nn, pairs):
    adj = collections.defaultdict(set)
    for a, b in pairs:
        if a != b:
            adj[a].add(b)
            adj[b].add(a)
    best = 0
    for s in range(nn):
        d = {s: 0}
        q = [s]
        for x in q:
            for y in adj[x]:
                if y not in d:
                    d[y] = d[x] + 1
                    q.append(y)
        if len(d) != nn:
            return None
        best = max(best, max(d.values()))
    return best


def ghat(seed, secs):
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    worst = 0
    while time.time() < end:
        m_ = a6_flow.random_plane_map(rng, rng.choice([3, 5, 9, 15]))
        n = m_.n
        me = len(m_.edges)
        length = [0] * (2 * me)
        for end_ in ('tail', 'deg'):
            nn, arcs, pairs = m_.ghat(length, end=end_)
            g = nx.Graph()
            g.add_nodes_from(range(nn))
            g.add_edges_from(p for p in pairs if p[0] != p[1])
            c['maps'] += 1
            if not nx.check_planarity(g)[0]:
                c['FAIL.not_planar.' + end_] += 1
                print('NOT PLANAR', end_, m_.edges, m_.rot)
            dg = hop_diam(n, [(a, b) for a, b in m_.edges])
            dh = hop_diam(nn, pairs)
            if dh is None or dh > 3 * dg + 2:
                c['FAIL.hop.' + end_] += 1
                print('HOP', m_.edges, m_.rot, dg, dh)
            worst = max(worst, (dh - 3 * dg))
            simple = len({tuple(sorted(e)) for e in m_.edges}) == me
            c['simple'] += simple
            if nn > 7 * n:
                c['nodes_above_7n_simple' if simple else 'nodes_above_7n_with_parallels'] += 1
            # a loop only at degree 1, as the paper says
            for e in range(me):
                d = 2 * e
                if end_ == 'deg' and len(m_.rot[m_.tail(d)]) < len(m_.rot[m_.head(d)]):
                    d += 1
                if m_.sigma_inv(d) == d and len(m_.rot[m_.tail(d)]) != 1:
                    c['FAIL.loop_not_degree1'] += 1
    c['max_excess_over_3D'] = worst
    print('ghat', json.dumps(dict(sorted(c.items()))))


def depth():
    rng = random.Random(1)
    out = {}
    for n in (64, 256, 1024):
        fams = {
            'dipath': [(i, i + 1, 0) for i in range(n - 1)],
            'empty': [],
            'dicycle': [(i, (i + 1) % n, 0) for i in range(n)],
            'outtree': [((i - 1) // 2, i, 0) for i in range(1, n)],
            'intree': [(i, (i - 1) // 2, 0) for i in range(1, n)],
            'gridDAG': [(i, i + 1, 0) for i in range(n - 1) if (i + 1) % int(n ** .5)] + [(i, i + int(n ** .5), 0) for i in range(n - int(n ** .5))],
            'pairs': [(2 * i, 2 * i + 1, 0) for i in range(n // 2)] + [(2 * i + 1, 2 * i + 2, 0) for i in range(n // 2 - 1)],
        }
        for name, arcs in fams.items():
            ds = {}
            for cc in (None, 'input'):
                st = Stats()
                for _ in range(3):
                    alg3(n, arcs, rng, cc=cc, stats=st)
                ds[str(cc)] = st['alg3_maxdepth']
            out[f'{name},n={n}'] = ds
            print(name, n, ds, 'log2n', round(math.log2(n), 1), flush=True)


def merge(seed, secs):
    """Lemma 1 on clusters run separately, against one call with weight M on the arcs between clusters, M just above the range of the offsets."""
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        n = rng.randrange(2, 12)
        m = rng.randrange(0, 4 * n)
        k = rng.randrange(1, 5)
        lab = [rng.randrange(k) for _ in range(n)]
        arcs = [(rng.randrange(n), rng.randrange(n), rng.randrange(0, 20)) for _ in range(m)]
        off = [rng.randrange(0, 50) for _ in range(n)]
        inside = [a for a in arcs if lab[a[0]] == lab[a[1]]]
        cross = [a for a in arcs if lab[a[0]] != lab[a[1]]]
        sep = oracle(n, inside, off, Stats())
        M = max(off) - min(off) + 1
        one = oracle(n, inside + [(u, v, M) for u, v, w in cross], off, Stats())
        c['runs'] += 1
        if sep != one:
            c['FAIL.merge'] += 1
        # control: M too small
        M2 = max(0, max(off) - min(off) - 40)
        if oracle(n, inside + [(u, v, M2) for u, v, w in cross], off, Stats()) != sep:
            c['ctl_M_small_fires'] += 1
    print('merge', json.dumps(dict(sorted(c.items()))))


def verify(seed, secs):
    """If the oracle's answer for the source call were wrong in one value, potentials still check. The local tree check would catch it."""
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    ex = None
    while time.time() < end:
        n = rng.randrange(2, 8)
        arcs = [(rng.randrange(n), rng.randrange(n), rng.randrange(-3, 6)) for _ in range(rng.randrange(1, 3 * n))]
        if bf(n, arcs) is None:
            continue
        phi = scaling(n, arcs, bf_solver, Stats())
        xa = scale_x(arcs, n)
        xp = [(u, v, w + phi[u] - phi[v]) for u, v, w in xa]
        s = rng.randrange(n)
        off = [None] * n
        off[s] = 0
        d = oracle(n, xp, off, Stats())
        reach = [v for v in range(n) if d[v] < INF and v != s]
        if not reach:
            continue
        v = rng.choice(reach)
        bad = list(d)
        bad[v] += 2 * (n + 1)      # the output floor changes by one
        c['runs'] += 1
        # stated checks: potentials only
        pot_ok = all(w >= 0 for u, v_, w in xp)
        c['stated_check_passes_on_wrong_answer'] += pot_ok
        ex = ex or (n, arcs, s, v)
        # local tree check of the repair
        ok = bad[s] == 0
        for u, y, w in xp:
            if bad[u] < INF and bad[u] + w < bad[y]:
                ok = False
        for y in range(n):
            if y != s and bad[y] < INF and not any(u_ < INF for u_ in [bad[a] for a, b, w in xp if b == y and bad[a] + w == bad[y]]):
                ok = False
        c['tree_check_catches'] += (not ok)
        # and the repair never rejects a right answer
        ok2 = d[s] == 0
        for u, y, w in xp:
            if d[u] < INF and d[u] + w < d[y]:
                ok2 = False
        for y in range(n):
            if y != s and d[y] < INF and not any(d[a] + w == d[y] for a, b, w in xp if b == y and d[a] < INF):
                ok2 = False
        c['FAIL.tree_check_rejects_right'] += (not ok2)
    print('verify', json.dumps(dict(sorted(c.items()))), 'example', ex)


def small3():
    """The smallest instance with equal index for different components, in print, with the arc between them."""
    rng = random.Random(1)
    net = [(0, 1), (1, 2), (2, 3)]
    kept = []
    seen = collections.Counter()
    for _ in range(2000):
        r = alg3(4, kept, rng, cc='input', size_of='own')
        lab = collections.defaultdict(list)
        for v, x in enumerate(r):
            lab[x].append(v)
        groups = sorted(tuple(g) for g in lab.values() if len(g) > 1)
        seen[str(groups)] += 1
    print('four isolated vertices in G minus E_rem, Cor. 33, own size: equal labels', dict(seen))
    # n = 3 never collides?
    res = collections.Counter()
    for _ in range(2000):
        r = alg3(3, [], rng, cc='input', size_of='own')
        res[len(set(r))] += 1
    print('three isolated vertices: number of distinct labels', dict(res))


if __name__ == '__main__':
    p = sys.argv[1]
    if p == 'ghat':
        ghat(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'depth':
        depth()
    elif p == 'merge':
        merge(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'verify':
        verify(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'small3':
        small3()
