"""Proposition 4, deterministic part, against an WORST-CASE decomposition: anything allowed by the first bullet of Lemma 2.

The chooser picks at every (level, repetition) any ordered partition with weak diameter <= 2^level in G>=0, and at level L any
topological order of the strong components, with random gaps in the indices. For t and R far below the theory the success event may
hold or fail. Claim tested: if the event holds on all levels then A(l) and B(l) hold on all levels and the final potential is right.

Also, on non-restricted inputs (negative cycles): oracle preconditions, and the bound |pot| <= n(t+1) + n*max idx.
Control: 'nominimum' (only Phi[0]), 'badorder' (index shift with the wrong sign), 'tooLow' (t = 0 on level 1) must fire.
usage: a2_worst_decomp.py <seed> <seconds>
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


def weakdist(n, ge):
    return [oracle(n, ge, [0 if v == s else None for v in range(n)], Stats()) for s in range(n)]


def chooser(n, ge, rng):
    D = weakdist(n, ge)
    comp = tarjan_order(n, ge)

    def decomp(l, r, d):
        nlev = 1
        while 2 ** nlev < 2 * n * n:
            nlev += 1
        if l == nlev:
            # strong components, any linear extension, random gaps
            ks = sorted(set(comp))
            arcs = {(comp[u], comp[v]) for u, v, w in ge if comp[u] != comp[v]}
            order = random_topo(ks, arcs, rng)
            idx_of = {}
            cur = 0
            for k in order:
                cur += rng.choice([1, 1, 1, 2, n ** 3 + 1])
                idx_of[k] = cur
            return [idx_of[comp[v]] for v in range(n)]
        style = rng.randrange(4)
        vs = list(range(n))
        rng.shuffle(vs)
        cl = []
        for v in vs:
            cands = [c for c in cl if all(D[v][x] <= d and D[x][v] <= d for x in c)]
            if cands and (style != 0):
                # style 1: join when possible; style 2: join only sometimes; style 3: largest cluster first
                if style == 1 or (style == 2 and rng.random() < 0.5) or style == 3:
                    (max(cands, key=len) if style == 3 else rng.choice(cands)).append(v)
                    continue
            cl.append([v])
        rng.shuffle(cl)
        if rng.random() < 0.5:
            # order so that many arcs with weight > 0 are cut: sort by a random potential, or reverse a topological order
            base = tarjan_order(n, ge)
            sign = rng.choice([1, -1])
            cl.sort(key=lambda c: (sign * min(base[x] for x in c), rng.random()))
        idx = [0] * n
        cur = 0
        for c in cl:
            cur += rng.choice([1, 1, 1, 2, n ** 3 + 1])
            for x in c:
                idx[x] = cur
        return idx
    return decomp


def random_topo(nodes, arcs, rng):
    indeg = {k: 0 for k in nodes}
    adj = collections.defaultdict(list)
    for a, b in arcs:
        indeg[b] += 1
        adj[a].append(b)
    ready = [k for k in nodes if indeg[k] == 0]
    out = []
    while ready:
        i = rng.randrange(len(ready))
        x = ready.pop(i)
        out.append(x)
        for y in adj[x]:
            indeg[y] -= 1
            if indeg[y] == 0:
                ready.append(y)
    assert len(out) == len(nodes)
    return out


def min_cuts_on_tight(n, inside, dist, idx):
    """For each v the least number of arcs with idx[u] > idx[v'] on a tight path from a vertex with dist 0."""
    tight = [(u, v) for u, v, w in inside if dist[u] + w == dist[v]]
    x = [0 if dist[v] == 0 else INF for v in range(n)]
    for _ in range(n + 1):
        ch = False
        for u, v in tight:
            y = x[u] + (1 if idx[u] > idx[v] else 0)
            if x[u] < INF and y < x[v]:
                x[v] = y
                ch = True
        if not ch:
            break
    return x


def run_one(n, arcs, rng, t, R, c, mode=''):
    ge = [(u, v, max(w, 0)) for u, v, w in arcs]
    dec = chooser(n, ge, rng)
    prev_idx = []
    this_idx = []
    cur_level = [1]
    event = [True]
    inexact = [False]

    def hook(l, r, idx, best, pot, inside, kept):
        nonlocal prev_idx, this_idx
        if l != cur_level[0]:
            prev_idx, this_idx = this_idx, []
            cur_level[0] = l
        this_idx.append(list(idx))
        dist = bf(n, inside)
        assert dist is not None
        c['values'] += n
        if best != dist:
            inexact[0] = True
            c['A_miss_runs_steps'] += 1
        if any(b < d for b, d in zip(best, dist)):
            c['FAIL.below_dist'] += 1
        # B: arcs not cut have w_pot >= 0
        for u, v, w in arcs:
            if idx[u] <= idx[v]:
                c['arcs'] += 1
                if w + pot[u] - pot[v] < 0:
                    inexact[0] = True
        # event at this level with the previous repetitions
        if l == 1:
            hops_ok = True
            # A(1) needs t >= 2; if t < 2 treat as event failing
            if t < 2:
                event[0] = False
        else:
            need = [INF] * n
            for pi in prev_idx:
                x = min_cuts_on_tight(n, inside, dist, pi)
                need = [min(a, b) for a, b in zip(need, x)]
            if max(need) > t:
                event[0] = False

    phi = restricted(n, arcs, R=R, t=t, c=1.0, rng=rng, decomp=dec, hook=hook, st=Stats())
    bad = any(w + phi[u] - phi[v] < 0 for u, v, w in arcs)
    c['runs'] += 1
    c['event' if event[0] else 'noevent'] += 1
    if bad:
        c['wrong_output'] += 1
    if inexact[0]:
        c['inexact_runs'] += 1
    if event[0] and (bad or inexact[0]):
        c['FAIL.event_but_inexact'] += 1
        print('EVENT BUT INEXACT', n, arcs, t, R)
    if not event[0] and inexact[0]:
        c['inexact_and_noevent'] += 1
    return bad


def gen_restricted(rng):
    n = rng.randrange(2, 8)
    kind = rng.randrange(3)
    arcs = []
    m = rng.randrange(1, 3 * n + 1)
    if kind == 0:
        for _ in range(m):
            arcs.append((rng.randrange(n), rng.randrange(n), rng.randrange(-1, n + 1)))
    else:
        order = list(range(n))
        rng.shuffle(order)
        p = [0] * n
        step = rng.choice([2, 2, 3, 1])
        for i, v in enumerate(order):
            p[v] = i * step if kind == 1 else rng.randrange(0, 2 * n)
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            sl = rng.choice([0, 0, 0, 1, 2])
            w = 1 + sl + p[u] - p[v]
            w = max(w, -1) if rng.random() < 0.0 else w
            if -1 <= w <= n:
                arcs.append((u, v, w))
    return n, arcs


def bound_nonrestricted(rng, c):
    """Negative cycles: r >= -1, r <= n, but no cycle condition. Bound and oracle preconditions, chooser decomposition."""
    n = rng.randrange(2, 8)
    m = rng.randrange(1, 3 * n + 1)
    arcs = [(rng.randrange(n), rng.randrange(n), rng.choice([-1, -1, -1, 0, 1, n])) for _ in range(m)]
    if not has_neg_cycle(n, arcs):
        return
    ge = [(u, v, max(w, 0)) for u, v, w in arcs]
    dec = chooser(n, ge, rng)
    t = rng.choice([0, 1, 2, 8])
    worst = [0]
    mi = [0]

    def hook(l, r, idx, best, pot, inside, kept):
        mi[0] = max(mi[0], max(idx))
        for v in range(n):
            if not -(t + 1) * n <= best[v] <= 0:
                c['FAIL.bound_best'] += 1
                print('bound', n, arcs, best, t)
        worst[0] = max(worst[0], max(abs(x) for x in pot) - mi[0] * n)
    phi = restricted(n, arcs, R=2, t=t, rng=rng, decomp=dec, hook=hook, st=Stats())
    c['nr_runs'] += 1
    c['nr_max_over_idx'] = max(c['nr_max_over_idx'], worst[0])
    c['nr_wrong_expected'] += any(w + phi[u] - phi[v] < 0 for u, v, w in arcs)


def main(seed, secs):
    rng = random.Random(seed)
    c = collections.Counter()
    end = time.time() + secs
    # exhaustive for n = 2 and n = 3 with at most 4 arcs, all multisets with weights -1, 0, 1, n
    for n in (2, 3):
        cand = [(u, v, w) for u in range(n) for v in range(n) for w in (-1, 0, 1, n) if u != v or w >= 1]
        for k in range(1, 5):
            for arcs in itertools.combinations(cand, k):
                arcs = list(arcs)
                if is_restricted(n, arcs):
                    for t, R in ((0, 1), (1, 1), (2, 1), (2, 2)):
                        run_one(n, arcs, rng, t, R, c)
                    c['exh'] += 1
    while time.time() < end:
        n, arcs = gen_restricted(rng)
        if not arcs or not is_restricted(n, arcs):
            continue
        t = rng.choice([0, 1, 1, 2, 2, 3])
        R = rng.choice([1, 1, 2])
        run_one(n, arcs, rng, t, R, c)
        if rng.random() < 0.3:
            bound_nonrestricted(rng, c)
    print(json.dumps(dict(sorted(c.items()))))


if __name__ == '__main__':
    main(int(sys.argv[1]), float(sys.argv[2]))
