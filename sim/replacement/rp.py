#!/usr/bin/env python3
"""Check of notes/REPLACEMENT.md. Central simulation: values only, no rounds.

  rp.py SEED SECS [big]   Lemma 1, the labels of Lemma 2 with their oracle calls, Theorem 2, Corollaries 4 and 5, Lemma 3 and the interval step
  rp.py ctl SEED SECS     negative controls, each must fail

Truth is one Dijkstra (Bellman-Ford with negative weights) per arc of P, with that arc removed.
"""
import heapq
import json
import random
import sys
import time
from collections import Counter, deque
from fractions import Fraction

import networkx as nx

INF = 10**18


def adj(n, arcs, skip=()):
    out = [[] for _ in range(n)]
    for i, (u, v, w) in enumerate(arcs):
        if i not in skip:
            out[u].append((v, w))
    return out


def dij(n, out, src):
    d = [INF] * n
    for v, x in src.items():
        d[v] = min(d[v], x)
    h = [(x, v) for v, x in src.items()]
    heapq.heapify(h)
    while h:
        x, u = heapq.heappop(h)
        if x > d[u]:
            continue
        for v, w in out[u]:
            if x + w < d[v]:
                d[v] = x + w
                heapq.heappush(h, (x + w, v))
    return d


def bford(n, arcs, s, skip=()):
    d = [INF] * n
    d[s] = 0
    for _ in range(n):
        ch = False
        for i, (u, v, w) in enumerate(arcs):
            if i not in skip and d[u] < INF and d[u] + w < d[v]:
                d[v] = d[u] + w
                ch = True
        if not ch:
            return d
    raise AssertionError('negative cycle')


def base(r, big):
    """A connected planar graph as a list of edges. `contract` gives high degree at low diameter."""
    m = r.randint(3, 11 if big else 6)
    kind = r.choice(['grid', 'wheel', 'cyl', 'contract', 'contract'])
    if kind == 'wheel':
        k = r.randint(3, 60 if big else 14)
        E = [(0, i) for i in range(1, k + 1)] + [(i, i % k + 1) for i in range(1, k + 1)]
    elif kind == 'cyl':
        a, b = r.randint(2, m), r.randint(3, m + 2)
        id = lambda i, j: i * b + j % b
        E = [(id(i, j), id(i, j + 1)) for i in range(a) for j in range(b)]
        E += [(id(i, j), id(i + 1, j)) for i in range(a - 1) for j in range(b)]
    else:
        a, b = r.randint(2, m), r.randint(2, m)
        id = lambda i, j: i * b + j
        E = [(id(i, j), id(i, j + 1)) for i in range(a) for j in range(b - 1)]
        E += [(id(i, j), id(i + 1, j)) for i in range(a - 1) for j in range(b)]
        for i in range(a - 1):
            for j in range(b - 1):
                if r.random() < 0.5:
                    E.append(r.choice([(id(i, j), id(i + 1, j + 1)), (id(i + 1, j), id(i, j + 1))]))
        if kind == 'contract':
            rep = list(range(a * b))

            def find(x):
                while rep[x] != x:
                    rep[x] = rep[rep[x]]
                    x = rep[x]
                return x
            for u, v in r.sample(E, int(len(E) * r.uniform(0.1, 0.45))):
                rep[find(u)] = find(v)
            E = [(find(u), find(v)) for u, v in E if find(u) != find(v)]
    ids = {v: i for i, v in enumerate(sorted({x for e in E for x in e}))}
    E = sorted({tuple(sorted((ids[u], ids[v]))) for u, v in E})
    g = nx.Graph(E)
    assert nx.check_planarity(g)[0] and nx.is_connected(g)
    return len(ids), E


def orient(E, r, undirected=False, zero=False):
    hi = r.choice([3, 3, 20, 1000])
    lo = 0 if zero else 1
    arcs = []
    for u, v in E:
        for _ in range(r.choice([1, 1, 1, 2])):
            w = r.randint(lo, hi)
            if undirected:
                arcs += [(u, v, w), (v, u, w)]
                continue
            mode = r.randrange(4)
            if mode != 0:
                arcs.append((u, v, r.randint(lo, hi)))
            if mode != 1:
                arcs.append((v, u, r.randint(lo, hi)))
    return arcs


def tight_path(n, arcs, phi, s, t, r):
    """A shortest s-t path as arc ids, by a randomized search on tight arcs, simple even with zero weights."""
    out = [[] for _ in range(n)]
    for i, (u, v, w) in enumerate(arcs):
        if phi[u] < INF and phi[u] + w == phi[v]:
            out[u].append((v, i))
    par = {s: None}
    st = [s]
    while st:
        u = st.pop()
        r.shuffle(out[u])
        for v, i in out[u]:
            if v not in par:
                par[v] = i
                st.append(v)
    P = []
    x = t
    while x != s:
        P.append(par[x])
        x = arcs[par[x]][0]
    return P[::-1]


def residual(arcs, P, phi, mode=''):
    """H′ with reduced weights: arcs of P reversed at weight 0."""
    P = set(P)
    res = []
    for i, (u, v, w) in enumerate(arcs):
        if phi[u] >= INF:
            continue
        if i in P:
            if mode == 'keep':
                res.append((u, v, 0))
            if mode != 'noreverse':
                res.append((v, u, 0))
        else:
            res.append((u, v, w + phi[u] - phi[v]))
    return res


def hierarchy(n, E, r, leaf):
    """Bags as in (V1) to (V3): each child is a component of X minus its hubs. `chain[v]` lists the bags that hold v in X′."""
    nb = [[] for _ in range(n)]
    for u, v in E:
        nb[u].append(v)
        nb[v].append(u)
    bags = []
    chain = [[] for _ in range(n)]

    def rec(C, depth, phub):
        C = set(C)
        if len(C) <= leaf:
            H = sorted(C)
        else:
            lev = {min(C, key=lambda _: r.random()): 0}
            q = deque(lev)
            while q:
                u = q.popleft()
                for v in nb[u]:
                    if v in C and v not in lev:
                        lev[v] = lev[u] + 1
                        q.append(v)
            layers = {}
            for v, l in lev.items():
                layers.setdefault(l, []).append(v)
            top = max(layers)
            H = layers[r.choice([top // 2, (top + 1) // 2, max(top // 2 - 1, 0)])]
            if len(H) == len(C):
                H = H[:len(H) // 2]
        i = len(bags)
        bags.append({'depth': depth, 'V': C, 'H': sorted(H), 'phub': set(phub)})
        for v in C:
            chain[v].append(i)
        rest = C - set(H)
        seen = set()
        for x in rest:
            if x in seen:
                continue
            seen.add(x)
            comp = [x]
            for u in comp:
                for v in nb[u]:
                    if v in rest and v not in seen:
                        seen.add(v)
                        comp.append(v)
            rec(comp, depth + 1, H)
    rec(range(n), 0, [])
    return bags, chain


def labels(n, res, bags, c, mode=''):
    """Exact labels as in Lemma 2: per depth and hub index one oracle call in each direction, with one source per bag."""
    depths = {}
    for i, b in enumerate(bags):
        depths.setdefault(b['depth'], []).append(i)
    out, inn = {}, {}
    for depth, ids in depths.items():
        owner = {v: i for i in ids for v in bags[i]['V']}
        if mode == 'leak':
            # the bag also holds the hubs of its parent, so that bags of a depth share vertices
            own = [set() for _ in range(n)]
            for i in ids:
                for v in bags[i]['V'] | bags[i]['phub']:
                    own[v].add(i)
            arcs = [(u, v, w) for u, v, w in res if own[u] & own[v]]
        else:
            arcs = [(u, v, w) for u, v, w in res if u in owner and v in owner and owner[u] == owner[v]]
        f, g = adj(n, arcs), adj(n, [(v, u, w) for u, v, w in arcs])
        for k in range(max(len(bags[i]['H']) for i in ids)):
            src = {bags[i]['H'][k]: 0 for i in ids if k < len(bags[i]['H'])}
            df, dg = dij(n, f, src), dij(n, g, src)
            c['n.calls'] += 2
            for i in ids:
                if k < len(bags[i]['H']):
                    for v in bags[i]['V']:
                        out[v, i, k] = df[v]
                        inn[v, i, k] = dg[v]
    return out, inn


def query(x, y, bags, chain, out, inn, mode=''):
    com = sorted(set(chain[x]) & set(chain[y]))
    if mode == 'lowest':
        com = com[-1:]
    best = INF
    for i in com:
        for k in range(len(bags[i]['H'])):
            best = min(best, inn[x, i, k] + out[y, i, k])
    return best


def intervals(k, cand, mode=''):
    """The step of Theorem 3: for each arc i of P the minimum over intervals [a, b) that hold i, level by level, as (M) does it."""
    ans = [INF] * k
    t = 0
    while (1 << t) <= k:
        X, Y = {}, {}
        for a, b, x in cand:
            if (a ^ b) >> t == 1:
                X[a] = min(X.get(a, INF), x)
                Y[b] = min(Y.get(b, INF), x)
        for seg in range((k >> (t + 1)) + 1):
            lo, m, hi = seg << (t + 1), (seg << (t + 1)) + (1 << t) - 1, ((seg + 1) << (t + 1)) - 1
            run = INF
            for i in range(lo, min(m, k - 1) + 1):
                run = min(run, X.get(i, INF))
                ans[i] = min(ans[i], run)
            run = INF
            for i in range(min(hi, k), m, -1):
                if i < k and mode != 'inclusive':
                    ans[i] = min(ans[i], run)
                run = min(run, Y.get(i, INF))
                if i < k and mode == 'inclusive':
                    ans[i] = min(ans[i], run)
        t += 1
    return ans


def undirected_rp(n, arcs, s, t, P, r, mode=''):
    """Theorem 3: two shortest-path trees and the intervals. Arcs of an edge sit in pairs: ids 2j and 2j + 1."""
    ds = dij(n, adj(n, arcs), {s: 0})
    dt = dij(n, adj(n, arcs), {t: 0})
    alpha = [-1] * n
    alpha[s] = 0
    for i, a in enumerate(P):
        alpha[arcs[a][1]] = i + 1
    inb = [[] for _ in range(n)]
    for u, v, w in arcs:
        if ds[u] + w == ds[v]:
            inb[v].append(u)
    for v in sorted(range(n), key=lambda v: ds[v]):
        if alpha[v] < 0:
            alpha[v] = alpha[r.choice(inb[v])]
    pe = {a // 2 for a in P}
    cand = []
    for j, (u, v, w) in enumerate(arcs):
        if j // 2 not in pe and alpha[u] < alpha[v]:
            cand.append((alpha[u], alpha[v], ds[u] + w + dt[v]))
    return intervals(len(P), cand, mode)


def approx(n, res, P, arcs, bags, chain, r, c, mode=''):
    """Theorem 2: lengths K w + 1, labels off by a factor up to 1 + eps/2, and rounding down by K."""
    eps = r.choice([Fraction(1), Fraction(1, 2), Fraction(1, 10)])
    K = 1 if mode == 'smallK' else int(4 * n / eps) + 1
    ell = [(u, v, K * w + 1) for u, v, w in res]
    cnt = Counter()
    out, inn = labels(n, ell, bags, cnt)
    rout = adj(n, res)
    fac = {}

    def noisy(key, val):
        if val >= INF:
            return INF
        f = fac.setdefault(key, 1 + eps / 2 * Fraction(r.randint(0, 8), 8))
        return val * f
    for a in P:
        x, y = arcs[a][:2]
        d1 = dij(n, rout, {x: 0})[y]
        best = INF
        for i in sorted(set(chain[x]) & set(chain[y])):
            for k in range(len(bags[i]['H'])):
                p, q = noisy((x, i, k, 0), inn[x, i, k]), noisy((y, i, k, 1), out[y, i, k])
                if p < INF and q < INF:
                    best = min(best, p + q)
        c['chk.approx'] += 1
        if d1 >= INF:
            if best < INF:
                c['FAIL.approx'] += 1
            continue
        got = int(best // K)
        if not d1 <= got <= (1 + eps) * d1:
            c['FAIL.approx'] += 1


def second_path(n, arcs, res, P, phi, best, c):
    """Corollary 4: the path of one more call, cut at the crossing, is simple and has weight min R."""
    i, R = best
    vs = [arcs[P[0]][0]] + [arcs[a][1] for a in P]
    pos = {v: j for j, v in enumerate(vs)}
    K = n + 1
    ell = [(u, v, K * w + 1) for u, v, w in res]
    d = dij(n, adj(n, ell), {vs[i]: 0})
    pi = [vs[i + 1]]
    while pi[-1] != vs[i]:
        y = pi[-1]
        pi.append(next(u for u, v, w in ell if v == y and d[u] + w == d[y]))
    pi.reverse()
    ka = max(j for j, v in enumerate(pi) if v in pos and pos[v] <= i)
    kb = min(j for j, v in enumerate(pi) if j > ka and v in pos)
    piece = pi[ka:kb + 1]
    path = vs[:pos[piece[0]]] + piece + vs[pos[piece[-1]] + 1:]
    onp = set(P)
    wt = 0
    for x, y in zip(path, path[1:]):
        k = pos.get(x)
        if k is not None and k + 1 < len(vs) and vs[k + 1] == y and k != i and x in vs[:pos[piece[0]]] + vs[pos[piece[-1]]:]:
            wt += arcs[P[k]][2]
        else:
            wt += min(w for j, (u, v, w) in enumerate(arcs) if j not in onp and u == x and v == y)
    c['chk.second'] += 1
    if len(set(path)) != len(path) or wt != R or path[0] != vs[0] or path[-1] != vs[-1]:
        c['FAIL.second'] += 1


def cycles(n, arcs, bags, chain, r, c, mode=''):
    """Corollary 5: labels of H itself, against a Dijkstra with the arc removed."""
    out, inn = labels(n, arcs, bags, Counter())
    for a in r.sample(range(len(arcs)), min(6, len(arcs))):
        x, y, w = arcs[a]
        q = query(y, x, bags, chain, out, inn)
        truth = dij(n, adj(n, arcs, (a,)), {y: 0})[x]
        c['chk.cycle'] += 1
        if (q + w if q < INF else INF) != (truth + w if truth < INF else INF):
            c['FAIL.cycle'] += 1


def lane_directed(r, big, c, mode=''):
    n, E = base(r, big)
    arcs = orient(E, r, zero=r.random() < 0.3)
    neg = r.random() < 0.2
    if neg:
        psi = [r.randint(-9, 9) for _ in range(n)]
        arcs = [(u, v, w + psi[u] - psi[v]) for u, v, w in arcs]
    s = r.randrange(n)
    phi = bford(n, arcs, s) if neg else dij(n, adj(n, arcs), {s: 0})
    far = [v for v in range(n) if v != s and phi[v] < INF]
    if not far:
        return
    t = r.choice(far)
    P = tight_path(n, arcs, phi, s, t, r)
    res = residual(arcs, P, phi, mode)
    assert all(w >= 0 for _, _, w in res)
    rout = adj(n, res)
    bags, chain = hierarchy(n, E, r, r.randint(1, 8))
    out, inn = labels(n, res, bags, c, mode)
    approx(n, res, P, arcs, bags, chain, r, c, mode)
    c['runs'] += 1
    c['max.hops'] = max(c['max.hops'], len(P))
    c['max.n'] = max(c['max.n'], n)
    c['max.bags'] = max(c['max.bags'], len(bags))
    best = (None, INF)
    for i, a in enumerate(P):
        x, y = arcs[a][:2]
        dd = bford(n, arcs, s, (a,)) if neg else dij(n, adj(n, arcs, (a,)), {s: 0})
        truth = dd[t]
        d1 = dij(n, rout, {x: 0})
        mine = d1[y] + phi[t] if d1[y] < INF else INF
        c['chk.lemma1'] += 1
        if mine != truth:
            c['FAIL.lemma1'] += 1
        ql = query(x, y, bags, chain, out, inn, mode)
        c['chk.labels'] += 1
        if ql != d1[y]:
            c['FAIL.labels'] += 1
        if truth < best[1]:
            best = (i, truth)
    if best[1] < INF and not mode:
        second_path(n, arcs, res, P, phi, best, c)
    if not neg and not mode:
        cycles(n, arcs, bags, chain, r, c)
    for _ in range(5):
        x, y = r.randrange(n), r.randrange(n)
        if phi[x] < INF and phi[y] < INF:
            c['chk.pairs'] += 1
            if query(x, y, bags, chain, out, inn, mode) != dij(n, rout, {x: 0})[y]:
                c['FAIL.pairs'] += 1


def lane_undirected(r, big, c, mode=''):
    n, E = base(r, big)
    arcs = orient(E, r, undirected=mode != 'asym', zero=mode == 'zero')
    if mode == 'asym':
        arcs = []
        for u, v in E:
            arcs += [(u, v, r.randint(1, 9)), (v, u, r.randint(1, 9))]
    s = r.randrange(n)
    t = r.choice([v for v in range(n) if v != s])
    phi = dij(n, adj(n, arcs), {s: 0})
    P = tight_path(n, arcs, phi, s, t, r)
    mine = undirected_rp(n, arcs, s, t, P, r, mode)
    c['runs.un'] += 1
    for i, a in enumerate(P):
        truth = dij(n, adj(n, arcs, (a, a ^ 1)), {s: 0})[t]
        c['chk.un'] += 1
        if mine[i] != truth:
            c['FAIL.un'] += 1


def run(seed, secs, big):
    r = random.Random(seed)
    c = Counter()
    end = time.time() + secs
    while time.time() < end:
        lane_directed(r, big, c)
        lane_undirected(r, big, c)
    return c


def controls(seed, secs):
    r = random.Random(seed)
    res = {}
    for name, lane in [('noreverse', lane_directed), ('keep', lane_directed), ('lowest', lane_directed), ('leak', lane_directed), ('smallK', lane_directed),
                       ('asym', lane_undirected), ('inclusive', lane_undirected), ('zero', lane_undirected)]:
        c = Counter()
        end = time.time() + secs
        while time.time() < end:
            lane(r, False, c, name)
        res[name] = dict(sorted(c.items()))
    return res


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3]))))
    else:
        c = run(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)
        print(json.dumps(dict(sorted(c.items()))))
