"""Test of the first bullet of Lemma 2 through [3, Cor. 33]: labels of different strong components.

Reading 1 (cc='input'): components of the input digraph G minus E_rem, which is what Cor. 33 writes.
Reading 2 (cc='net'): components of the network.
In the base case the interval is [l N^2, (l + m - 1) N^2], with m the size of the component ('own') or of the set R_j ('parent').

Reports how often different strong components share a label, and whether there are arcs of G between them.
usage: a3_labels.py small | a3_labels.py rates | a3_labels.py full <seconds>
"""
import collections
import itertools
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *


def check(n, kept, allarcs, r, c, tag):
    comp = tarjan_order(n, kept)
    # order
    for u, v, w in kept:
        if comp[u] != comp[v]:
            c[tag, 'kept_arc_between_scc'] += 1
            if not r[u] > r[v]:
                c[tag, 'FAIL.order'] += 1
    # collisions
    lab = collections.defaultdict(set)
    for v in range(n):
        lab[r[v]].add(comp[v])
    coll = [k for k, s in lab.items() if len(s) > 1]
    if coll:
        c[tag, 'runs_with_collision'] += 1
        cl = set(coll)
        arcs_between = [(u, v, w) for u, v, w in allarcs if r[u] == r[v] and comp[u] != comp[v]]
        if arcs_between:
            c[tag, 'runs_with_arc_between_colliding'] += 1
            c[tag, 'neg_arc_between_colliding'] += sum(1 for a in arcs_between if a[2] < 0)
    c[tag, 'runs'] += 1


def small():
    """Smallest instances: 4 isolated vertices in the input digraph, on network paths; out-star; path with all arcs removed."""
    c = collections.Counter()
    rng = random.Random(5)
    insts = {
        'net path 4, E_rem = all': (4, [], [(0, 1), (1, 2), (2, 3)]),
        'net cycle 4, E_rem = all': (4, [], [(0, 1), (1, 2), (2, 3), (3, 0)]),
        'net star 5, E_rem = all': (5, [], [(0, i) for i in range(1, 5)]),
        'out-star 5 kept': (5, [(0, i, 0) for i in range(1, 5)], [(0, i) for i in range(1, 5)]),
        'n/2 two-cycles, line of them, 40': (40, sum(([(2 * i, 2 * i + 1, 0), (2 * i + 1, 2 * i, 0)] for i in range(20)), []),
                                               [(2 * i, 2 * i + 1) for i in range(20)] + [(2 * i + 1, 2 * i + 2) for i in range(19)]),
    }
    res = {}
    for name, (n, kept, net) in insts.items():
        allarcs = [(a, b, 1) for a, b in net]
        row = {}
        for cc, size in (('input', 'own'), ('input', 'parent'), ('net', 'own'), ('net', 'parent'), (None, 'own')):
            tag = (cc, size)
            ct = collections.Counter()
            for _ in range(4000 if n < 10 else 1500):
                r = alg3(n, kept, rng, cc=cc, net=net, size_of=size)
                check(n, kept, allarcs, r, ct, tag)
            row[str(tag)] = {k[1]: v for k, v in sorted(ct.items(), key=str)}
        res[name] = row
    print(json.dumps(res, indent=0))


def rates(trials=3000):
    """Collision rate for many components of size two in one R_j, against the 'with high probability' of Cor. 33, as n grows."""
    rng = random.Random(6)
    out = {}
    for k in (5, 10, 20, 40, 80):
        n = 2 * k
        kept = sum(([(2 * i, 2 * i + 1, 0), (2 * i + 1, 2 * i, 0)] for i in range(k)), [])
        # network: no edges between the pairs inside R_j unless both ends fall there; ring of pairs
        net = [(2 * i, 2 * i + 1) for i in range(k)] + [(2 * i + 1, (2 * i + 2) % n) for i in range(k)]
        for cc, size in (('input', 'own'), ('input', 'parent'), ('net', 'own')):
            coll = 0
            with_arc = 0
            for _ in range(trials if n <= 80 else trials // 3):
                r = alg3(n, kept, rng, cc=cc, net=net, size_of=size)
                lab = collections.defaultdict(set)
                for i in range(k):
                    lab[r[2 * i]].add(i)
                bad = {x for x, s in lab.items() if len(s) > 1}
                coll += bool(bad)
                with_arc += any(r[a] == r[b] and a // 2 != b // 2 for a, b in net)
            out[f'k={k},{cc},{size}'] = (coll, with_arc, trials)
    print(json.dumps(out, indent=0))


def plane_arcs(rng):
    """Restricted instances on grids: a snake of -1 arcs broken by arcs of positive weight."""
    a, b = rng.randrange(3, 8), rng.randrange(3, 8)
    n = a * b
    order = [i * b + (j if i % 2 == 0 else b - 1 - j) for i in range(a) for j in range(b)]
    pat = rng.choice([1, 2, 3, 5])
    p = [0] * n
    cur = 0
    for i, v in enumerate(order):
        p[v] = cur
        cur += 2 if (i + 1) % (pat + 1) else 2 - pat - rng.randrange(0, 2)
    net = []
    arcs = []
    for i in range(a):
        for j in range(b):
            x = i * b + j
            for y in ([x + 1] if j + 1 < b else []) + ([x + b] if i + 1 < a else []):
                net.append((x, y))
                for u, v in ((x, y), (y, x)):
                    w = 1 + p[u] - p[v]
                    if w < -1:
                        w = -1 + 0
                        continue
                    if w <= n:
                        arcs.append((u, v, w))
    return n, arcs, net


def full(secs, t=8, R=3, c=1.0, seed=7):
    """Proposition 4 with the labels of Cor. 33, against the direct order. Wrong final potential counts."""
    rng = random.Random(seed)
    res = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        n, arcs, net = plane_arcs(rng)
        if not is_restricted(n, arcs):
            res['not_restricted'] += 1
            continue
        for label in ('tarjan', 'seq', 'cor33input', 'cor33net', 'cor33input_parent'):
            st = Stats()
            phi = restricted(n, arcs, R=R, t=t, c=c, rng=rng, label=label, net=net, st=st)
            res[label, 'runs'] += 1
            if any(w + phi[u] - phi[v] < 0 for u, v, w in arcs):
                res[label, 'wrong'] += 1
            res[label, 'maxdepth'] = max(res[label, 'maxdepth'], st['alg3_maxdepth'])
    print(json.dumps({str(k): v for k, v in sorted(res.items(), key=str)}, indent=0))


if __name__ == '__main__':
    if sys.argv[1] == 'small':
        small()
    elif sys.argv[1] == 'rates':
        rates()
    else:
        full(float(sys.argv[2]))
