"""Instance families with explicit rotation systems (no networkx in this environment)."""
import math
import random
from nd_core import Inst


class M:
    """Plane map in the format of sim.py: dart 2e leaves ends[e][0], corner k of v is between rot[v][k] and rot[v][k+1]."""

    def __init__(s, n=0, ends=None, rot=None):
        s.n = n
        s.ends = list(ends or [])
        s.rot = [list(r) for r in (rot or [])]

    def pos(s):
        return {d: (v, k) for v, r in enumerate(s.rot) for k, d in enumerate(r)}

    def faces(s):
        pos = s.pos()
        seen = set()
        F = []
        for d0 in range(2 * len(s.ends)):
            if d0 in seen:
                continue
            cyc = []
            d = d0
            while d not in seen:
                seen.add(d)
                cyc.append(d)
                v, k = pos[d ^ 1]
                r = s.rot[v]
                d = r[(k + 1) % len(r)]
            F.append(cyc)
        return F

    def head(s, d):
        return s.ends[d >> 1][(d & 1) ^ 1]

    def tail(s, d):
        return s.ends[d >> 1][d & 1]

    def corner_after(s, d):
        """corner (v,k) that follows dart d in its face walk."""
        v, k = s.pos()[d ^ 1]
        return v, k

    def add_pendant_after(s, d):
        v, k = s.corner_after(d)
        e = len(s.ends)
        s.ends.append((v, s.n))
        s.rot[v].insert(k + 1, 2 * e)
        s.rot.append([2 * e + 1])
        s.n += 1
        return s.n - 1, e

    def add_chord_after(s, d1, d2):
        """edge between the corners after the darts d1, d2 of one face; the ends must differ."""
        u, i = s.corner_after(d1)
        v, j = s.corner_after(d2)
        assert u != v
        e = len(s.ends)
        s.ends.append((u, v))
        s.rot[u].insert(i + 1, 2 * e)
        s.rot[v].insert(j + 1, 2 * e + 1)
        return e

    def has_edge(s, u, v):
        return any({a, b} == {u, v} for a, b in s.ends)

    def add_star(s, cyc, targets):
        """new vertex in the face with walk cyc, joined to the corners after the darts in targets."""
        d0 = targets[0]
        w, e = s.add_pendant_after(d0)
        for d in targets[1:]:
            F = s.faces()
            fc = next(f for f in F if d in f)
            dw = next(x for x in fc if s.head(x) == w)
            s.add_chord_after(dw, d)
        return w

    def remove_edges(s, rem):
        keep = [e for e in range(len(s.ends)) if e not in rem]
        idx = {e: q for q, e in enumerate(keep)}
        s.rot = [[2 * idx[d >> 1] + (d & 1) for d in r if d >> 1 in idx] for r in s.rot]
        s.ends = [s.ends[e] for e in keep]

    def subdivide(s, e):
        u, v = s.ends[e]
        w = s.n
        s.n += 1
        ne = len(s.ends)
        s.ends[e] = (u, w)
        s.ends.append((w, v))
        k = s.rot[v].index(2 * e + 1)
        s.rot[v][k] = 2 * ne + 1
        s.rot.append([2 * e + 1, 2 * ne])

    def add_parallel(s, e):
        d = 2 * e
        pos = s.pos()
        # corners on the two sides of dart d in its face: after the dart before d, and after d
        F = s.faces()
        fc = next(f for f in F if d in f)
        q = fc.index(d)
        s.add_chord_after(fc[(q - 1) % len(fc)], d)

    def connected(s):
        if s.n == 0:
            return False
        adj = [[] for _ in range(s.n)]
        for a, b in s.ends:
            adj[a].append(b)
            adj[b].append(a)
        seen = {0}
        st = [0]
        while st:
            u = st.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        return len(seen) == s.n

    def euler(s):
        return s.n - len(s.ends) + len(s.faces())


def from_coords(pts, edges):
    n = len(pts)
    rot = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        rot[u].append(2 * e)
        rot[v].append(2 * e + 1)
    for v in range(n):
        def ang(d):
            w = edges[d >> 1][(d & 1) ^ 1]
            return math.atan2(pts[w][1] - pts[v][1], pts[w][0] - pts[v][0])
        rot[v].sort(key=ang)
    return M(n, edges, rot)


def grid_edges(a, b, rng, pd):
    idx = lambda i, j: i * b + j
    pts = [(j * 1.0, i * 1.0) for i in range(a) for j in range(b)]
    edges, kind = [], []
    for i in range(a):
        for j in range(b):
            if j + 1 < b:
                edges.append((idx(i, j), idx(i, j + 1)))
                kind.append('h')
            if i + 1 < a:
                edges.append((idx(i, j), idx(i + 1, j)))
                kind.append('v')
            if i + 1 < a and j + 1 < b and rng.random() < pd:
                if rng.random() < .5:
                    edges.append((idx(i, j), idx(i + 1, j + 1)))
                else:
                    edges.append((idx(i + 1, j), idx(i, j + 1)))
                kind.append('d')
    return pts, edges, kind


def fam_grid(rng, maxn=60, straight=False):
    a = rng.randint(2, 7)
    b = rng.randint(2, max(2, min(30, maxn // a)))
    pd = rng.choice([0, 0.3, 0.6, 1.0])
    if straight:
        pd = rng.choice([0, 1.0, 0.5])
    pts, edges, kind = grid_edges(a, b, rng, pd)
    mp = from_coords(pts, edges)
    idx = lambda i, j: i * b + j
    r = rng.random()
    if r < .5:
        S, T = idx(rng.randrange(a), 0), idx(rng.randrange(a), b - 1)
    elif r < .7:
        S, T = idx(0, 0), idx(a - 1, b - 1)
    else:
        S, T = rng.sample(range(a * b), 2)
    return mp, S, T, kind, pts


def fam_hubgrid(rng, maxn=60):
    """Classic st-network: a grid, s joined to the left column and t to the right column."""
    a = rng.randint(2, 6)
    b = rng.randint(2, max(2, min(20, (maxn - 2) // a)))
    pts, edges, kind = grid_edges(a, b, rng, rng.choice([0, .3, .6]))
    idx = lambda i, j: i * b + j
    S = len(pts)
    pts.append((-1.0, (a - 1) / 2))
    T = len(pts)
    pts.append((b * 1.0, (a - 1) / 2))
    for i in range(a):
        edges.append((S, idx(i, 0)))
        kind.append('s')
        edges.append((idx(i, b - 1), T))
        kind.append('s')
    return from_coords(pts, edges), S, T, kind, pts


def fam_rings(rng, maxn=60):
    """Concentric rings with spokes and a hub; an outer hub is added combinatorially."""
    L = rng.randint(3, 10)
    k = rng.randint(2, max(2, (maxn - 2) // L))
    pts, edges, kind = [], [], []
    idx = lambda r, i: r * L + (i % L)
    for r in range(k):
        for i in range(L):
            th = 2 * math.pi * i / L
            pts.append(((r + 1) * math.cos(th), (r + 1) * math.sin(th)))
    for r in range(k):
        for i in range(L):
            edges.append((idx(r, i), idx(r, i + 1)))
            kind.append('r')
    pi = rng.choice([.5, .8, 1.0])
    for r in range(k - 1):
        for i in range(L):
            if rng.random() < pi or i == 0:
                edges.append((idx(r, i), idx(r + 1, i)))
                kind.append('s')
    c = len(pts)
    pts.append((0.0, 0.0))
    for i in range(L):
        if rng.random() < pi or i == 0:
            edges.append((c, idx(0, i)))
            kind.append('s')
    mp = from_coords(pts, edges)
    if rng.random() < .5:
        # an outer hub in the outer face
        F = mp.faces()
        outer = max(F, key=len)
        ts = [d for d in outer]
        rng.shuffle(ts)
        ts = ts[:max(1, rng.randint(1, len(ts)))]
        T = mp.add_star(outer, ts)
        kind = kind + ['s'] * (len(mp.ends) - len(kind))
        S = c
    else:
        S = c
        T = idx(k - 1, rng.randrange(L))
    if rng.random() < .5:
        S, T = T, S
    return mp, S, T, kind, None


def fam_stacked(rng, maxn=60):
    n = rng.randint(4, maxn)
    mp = from_coords([(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)], [(0, 1), (1, 2), (2, 0)])
    while mp.n < n:
        F = [f for f in mp.faces() if len(f) == 3]
        f = rng.choice(F)
        mp.add_star(f, list(f))
    # delete some edges, keep connected
    frac = rng.choice([0, .1, .3, .5])
    cand = list(range(len(mp.ends)))
    rng.shuffle(cand)
    rem = set()
    for e in cand[:int(frac * len(cand))]:
        rem.add(e)
        tmp = M(mp.n, mp.ends, mp.rot)
        tmp.remove_edges(rem)
        if not tmp.connected():
            rem.discard(e)
    mp.remove_edges(rem)
    S, T = rng.sample(range(mp.n), 2)
    return mp, S, T, None, None


def fam_randmap(rng, maxn=60):
    nv = rng.randint(3, maxn)
    pch = rng.choice([.3, .5, .7, .85])
    mp = M(2, [(0, 1)], [[0], [1]])
    guard = 0
    while mp.n < nv and guard < 2000 and len(mp.ends) < 3 * nv:
        guard += 1
        F = mp.faces()
        f = rng.choice(F)
        if rng.random() < pch and len(f) >= 3:
            d1, d2 = rng.sample(f, 2)
            u, v = mp.corner_after(d1)[0], mp.corner_after(d2)[0]
            if u != v and not mp.has_edge(u, v):
                mp.add_chord_after(d1, d2)
                continue
        mp.add_pendant_after(rng.choice(f))
    # densify
    for _ in range(int(nv * rng.choice([0, .5, 1, 2]))):
        F = mp.faces()
        f = rng.choice(F)
        if len(f) < 3:
            continue
        d1, d2 = rng.sample(f, 2)
        u, v = mp.corner_after(d1)[0], mp.corner_after(d2)[0]
        if u != v and not mp.has_edge(u, v):
            mp.add_chord_after(d1, d2)
    S, T = rng.sample(range(mp.n), 2)
    return mp, S, T, None, None


def fam_outerplanar(rng, maxn=60):
    n = rng.randint(4, maxn)
    pts = [(math.cos(2 * math.pi * i / n), math.sin(2 * math.pi * i / n)) for i in range(n)]
    edges = [(i, (i + 1) % n) for i in range(n)]
    mp = from_coords(pts, edges)
    for _ in range(rng.randint(0, 2 * n)):
        F = mp.faces()
        big = [f for f in F if len(f) >= 4]
        if not big:
            break
        f = rng.choice(big)
        d1, d2 = rng.sample(f, 2)
        u, v = mp.corner_after(d1)[0], mp.corner_after(d2)[0]
        if u != v and not mp.has_edge(u, v):
            mp.add_chord_after(d1, d2)
    S, T = rng.sample(range(n), 2)
    return mp, S, T, None, None


def fam_theta(rng, maxn=60):
    """k internally disjoint s-t paths, some cross links between consecutive paths."""
    k = rng.randint(2, 7)
    l = rng.randint(1, max(1, (maxn - 2) // k))
    pts = [(-1.0, 0.0), (l * 1.0 + 1, 0.0)]
    edges = []
    idx = {}
    for p in range(k):
        for q in range(l):
            idx[(p, q)] = len(pts)
            pts.append((q * 1.0, (p - (k - 1) / 2) * (1 + abs(q - (l - 1) / 2) * 0)))
    for p in range(k):
        edges.append((0, idx[(p, 0)]))
        for q in range(l - 1):
            edges.append((idx[(p, q)], idx[(p, q + 1)]))
        edges.append((idx[(p, l - 1)], 1))
    plink = rng.choice([0, .3, .6])
    for p in range(k - 1):
        for q in range(l):
            if rng.random() < plink:
                edges.append((idx[(p, q)], idx[(p + 1, q)]))
    return from_coords(pts, edges), 0, 1, None, None


FAMS = dict(grid=fam_grid, hubgrid=fam_hubgrid, rings=fam_rings, stacked=fam_stacked, randmap=fam_randmap,
            outerplanar=fam_outerplanar, theta=fam_theta)


def decorate(mp, rng, multi=False):
    for _ in range(rng.choice([0, 0, 1, 3])):
        mp.subdivide(rng.randrange(len(mp.ends)))
    for _ in range(rng.choice([0, 0, 1, 2])):
        F = mp.faces()
        mp.add_pendant_after(rng.choice(rng.choice(F)))
    if multi:
        for _ in range(rng.choice([0, 1, 2, 4])):
            mp.add_parallel(rng.randrange(len(mp.ends)))
    return mp


def caps_for(mp, rng, kind=None, S=0):
    m = len(mp.ends)
    sc = rng.choice(['one', 'one', 'one', 'z01', 'r12', 'r123', 'zero_some', 'big_some', 'gen', 'layer', 'aniso', 'aniso', 'aniso2'])
    if sc == 'one':
        return sc, [1] * m
    if sc == 'z01':
        return sc, [rng.randint(0, 1) for _ in range(m)]
    if sc == 'r12':
        return sc, [rng.randint(1, 2) for _ in range(m)]
    if sc == 'r123':
        return sc, [rng.randint(1, 3) for _ in range(m)]
    if sc == 'zero_some':
        return sc, [0 if rng.random() < 0.3 else 1 for _ in range(m)]
    if sc == 'gen':
        return sc, [rng.randint(1, 10 ** 6) for _ in range(m)]
    if sc == 'big_some':
        return sc, [rng.choice([1, 1, 1, 2, 50]) for _ in range(m)]
    # capacity by BFS layer from s: many equal-capacity cuts
    if sc == 'layer':
        adj = [[] for _ in range(mp.n)]
        for e, (a, b) in enumerate(mp.ends):
            adj[a].append(b)
            adj[b].append(a)
        dist = {S: 0}
        q = [S]
        for u in q:
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        return sc, [1 + min(dist.get(a, 0), dist.get(b, 0)) % 3 for a, b in mp.ends]
    if kind is not None and len(kind) >= m:
        if sc == 'aniso':
            cost = dict(h=5, v=1, d=2, r=5, s=1)
        else:
            cost = dict(h=2, v=1, d=2, r=2, s=1)
        return sc, [cost.get(kind[e], 1) for e in range(m)]
    return 'r12', [rng.randint(1, 2) for _ in range(m)]


def make(seed, fam=None, maxn=60):
    rng = random.Random(seed)
    for _ in range(40):
        name = fam or rng.choice(['grid', 'grid', 'hubgrid', 'rings', 'rings', 'stacked', 'randmap', 'outerplanar', 'theta'])
        mp, S, T, kind, pts = FAMS[name](rng, maxn)
        if rng.random() < .35:
            lenbefore = len(mp.ends)
            decorate(mp, rng, multi=False)
            pts = None
            if kind is not None:
                kind = kind + ['s'] * (len(mp.ends) - len(kind))
        if mp.n > maxn + 8 or not mp.connected() or mp.euler() != 2 or S == T:
            continue
        sc, cap = caps_for(mp, rng, kind, S)
        I = Inst(mp.n, mp.ends, mp.rot, cap, S, T, tag=name + ':' + sc)
        return I, rng
    raise RuntimeError('generator failed')
