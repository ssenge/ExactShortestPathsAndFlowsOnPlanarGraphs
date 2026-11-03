"""Combinatorial (non-geometric) families of plane graphs given as rotation systems."""
import sys, random, collections
sys.dont_write_bytecode = True
from mine import mkidx, corner_faces, is_planar_rot


def add_edge(rot, u, ju, v, jv):
    rot[u] = rot[u][:ju] + [v] + rot[u][ju:]
    rot[v] = rot[v][:jv] + [u] + rot[v][jv:]


def tree_rot(n, rng, shape):
    """random plane tree of a given shape; returns rot"""
    V = list(range(n)); rot = {v: [] for v in V}
    def link(u, v):
        rot[u].insert(rng.randrange(len(rot[u]) + 1), v); rot[v].insert(rng.randrange(len(rot[v]) + 1), u)
    if shape == 'path':
        for v in range(1, n): link(v - 1, v)
    elif shape == 'star':
        for v in range(1, n): link(0, v)
    elif shape == 'cater':
        sp = max(2, n // 3)
        for v in range(1, sp): link(v - 1, v)
        for v in range(sp, n): link(rng.randrange(sp), v)
    elif shape == 'spider':
        legs = rng.randint(3, max(3, n // 3)); cur = {}
        for v in range(1, n):
            l = (v - 1) % legs
            link(cur.get(l, 0), v); cur[l] = v
    elif shape == 'binary':
        for v in range(1, n): link((v - 1) // 2, v)
    elif shape == 'broom':
        h = n // 2
        for v in range(1, h): link(v - 1, v)
        for v in range(h, n): link(h - 1, v)
    elif shape == 'deep':  # random recursive tree biased to recent vertices (deep)
        for v in range(1, n): link(max(0, v - 1 - int(rng.expovariate(1.0))), v)
    else:  # uniform-ish random recursive tree
        for v in range(1, n): link(rng.randrange(v), v)
    return V, rot


def local_chords(V, rot, rng, cnt, gapmax, existing=None):
    """insert up to cnt edges between corners of one face that are 2..gapmax apart along the
    face walk (short chords, mostly light)."""
    E = set(frozenset((a, b)) for a in V for b in rot[a])
    added = 0; tries = 0
    while added < cnt and tries < 30 * cnt + 30:
        tries += 1
        fid, faces = corner_faces(rot, mkidx(rot))
        f = rng.choice(faces)
        if len(f) < 3:
            continue
        s = rng.randrange(len(f)); g = rng.randint(2, max(2, min(gapmax, len(f) - 1)))
        a = f[s]; b = f[(s + g) % len(f)]
        u, v = a[0], b[0]
        if u == v or frozenset((u, v)) in E:
            continue
        add_edge(rot, u, a[1], v, b[1]); E.add(frozenset((u, v))); added += 1
    return rot


def any_chords(V, rot, rng, cnt):
    return local_chords(V, rot, rng, cnt, 10 ** 9)


def wheel(n, rng):
    m = n - 1; hub = m
    rot = {v: [(v + 1) % m, hub, (v - 1) % m] for v in range(m)}
    rot[hub] = list(range(m))
    if not is_planar_rot(rot, mkidx(rot)):
        rot[hub] = rot[hub][::-1]
    return list(range(n)), rot


def nested(n, rng):
    """concentric cycles of length L joined by spokes (a 'web'), optionally a center vertex."""
    L = rng.randint(3, max(3, n // 3)); rings = max(1, (n - 1) // L)
    V = []; rot = {}
    def vid(i, t): return i * L + t
    N = rings * L
    for i in range(rings):
        for t in range(L):
            v = vid(i, t); V.append(v); rot[v] = []
    c = N; V.append(c); rot[c] = []
    E = []
    for i in range(rings):
        for t in range(L):
            E.append((vid(i, t), vid(i, (t + 1) % L)))
            if i + 1 < rings and (rng.random() < 0.7 or t == 0):
                E.append((vid(i, t), vid(i + 1, t)))
    for t in range(L):
        if rng.random() < 0.6 or t == 0:
            E.append((c, vid(0, t)))
    # geometric rotation from polar coordinates (center inside ring 0)
    import math
    pos = {c: (0.0, 0.0)}
    for i in range(rings):
        for t in range(L):
            a = 2 * math.pi * t / L; pos[vid(i, t)] = ((i + 1) * math.cos(a), (i + 1) * math.sin(a))
    nb = collections.defaultdict(list)
    for a, b in E:
        nb[a].append(b); nb[b].append(a)
    rot = {v: sorted(nb[v], key=lambda u: math.atan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0])) for v in V}
    return V, rot


def cactus(n, rng):
    """tree of cycles: start with a triangle, repeatedly hang a new cycle (or a pendant edge) at a
    random corner."""
    V = [0, 1, 2]; rot = {0: [1, 2], 1: [2, 0], 2: [0, 1]}
    if not is_planar_rot(rot, mkidx(rot)):
        rot = {0: [2, 1], 1: [0, 2], 2: [1, 0]}
    while len(V) < n:
        fid, faces = corner_faces(rot, mkidx(rot))
        f = rng.choice(faces); u, j = rng.choice(f)
        k = min(rng.choice([1, 1, 2, 3, 4, 6]), n - len(V))
        new = list(range(len(V), len(V) + k)); V += new
        if k == 1:
            rot[u].insert(j, new[0]); rot[new[0]] = [u]; continue
        ring = [u] + new + [u]
        for t in range(1, len(ring) - 1):
            rot[ring[t]] = [ring[t - 1], ring[t + 1]]
        old = rot[u]
        rot[u] = old[:j] + [new[0], new[-1]] + old[j:]
        if not is_planar_rot(rot, mkidx(rot)):
            rot[u] = old[:j] + [new[-1], new[0]] + old[j:]
            if not is_planar_rot(rot, mkidx(rot)):
                raise RuntimeError('cactus')
    return V, rot


def sibling_fan(n, rng):
    """root with many children, each child gets a small subtree, chords between consecutive
    children (triangles with the root) and some chords inside subtrees."""
    V, rot = tree_rot(n, rng, 'star' if rng.random() < 0.3 else 'cater')
    local_chords(V, rot, rng, rng.randint(1, n), 3)
    return V, rot


def heavy_onion(n, rng):
    """nested cycles around a small core so that o can lie deep inside a chain of chords."""
    V, rot = nested(n, rng)
    return V, rot


def hub_face(n, rng):
    """a hub with many corners in one face: a star whose leaves carry small gadgets, and local
    chords elsewhere."""
    V, rot = tree_rot(n, rng, 'star')
    # grow some leaves into paths
    return V, local_chords(V, rot, rng, rng.randint(0, n // 2), 4)


def tri_strip(n, rng):
    """long cycle (a path plus the closing edge) and chords that triangulate parts of it."""
    V = list(range(n)); rot = {v: [] for v in V}
    for v in range(1, n):
        rot[v - 1].append(v); rot[v].append(v - 1)
    fid, faces = corner_faces(rot, mkidx(rot))
    f = faces[0]
    a = [c for c in f if c[0] == 0][0]; b = [c for c in f if c[0] == n - 1][0]
    add_edge(rot, 0, a[1], n - 1, b[1])
    local_chords(V, rot, rng, rng.randint(0, n), rng.choice([2, 3, 5]))
    return V, rot


def onion(n, rng):
    """nested short cycles around a centre c (rings of length 3 or 4 joined by spokes), and a
    big plane tree hung in the outer face or in the innermost face, so ring chords are heavy or
    light depending on where o is."""
    L = rng.choice([3, 3, 4]); rings = rng.randint(1, max(1, n // (3 * L)))
    V = [0]; rot = {0: []}
    prev = None
    for i in range(rings):
        ring = list(range(len(V), len(V) + L)); V += ring
        for v in ring: rot[v] = []
        for t in range(L):
            a, b = ring[t], ring[(t + 1) % L]
            rot[a].append(b); rot[b].append(a)
        if prev is None:
            for v in ring: rot[0].append(v); rot[v].append(0)
        else:
            for t in range(L):
                if t == 0 or rng.random() < 0.5:
                    rot[prev[t]].append(ring[t]); rot[ring[t]].append(prev[t])
        prev = ring
    # geometric rotation: centre at origin, ring i at radius i+1
    import math
    pos = {0: (0.0, 0.0)}
    for v in V[1:]:
        i, t = (v - 1) // L, (v - 1) % L
        a = 2 * math.pi * t / L + 0.3 * i; rad = (2.5 if L == 3 else 1.6) ** i; pos[v] = (rad * math.cos(a), rad * math.sin(a))
    rot = {v: sorted(set(rot[v]), key=lambda u: math.atan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0])) for v in V}
    # hang a tree
    where = rng.choice(['out', 'out', 'in'])
    fid, faces = corner_faces(rot, mkidx(rot))
    if where == 'out':
        cand = [c for c in fid if c[0] in prev]
    else:
        cand = [c for c in fid if c[0] == 0]
    host = rng.choice(cand)
    hub, j = host
    m = n - len(V)
    if m > 0:
        w0 = len(V); V.append(w0); rot[w0] = [hub]; rot[hub].insert(j, w0)
        for t in range(1, m):
            w = len(V); u = rng.choice(V[w0:]); V.append(w); rot[w] = [u]
            rot[u].insert(rng.randrange(len(rot[u]) + 1), w)
    if rng.random() < 0.5:
        local_chords(V, rot, rng, rng.randint(0, n // 4), 3)
    return V, rot


def ears(n, rng):
    """a plane tree with many leaves and 'ears': chords between leaves that are consecutive
    around the outer face, so the face of o is bounded by many light chords."""
    V, rot = tree_rot(n, rng, rng.choice(['star', 'spider', 'cater', 'binary', 'rand']))
    local_chords(V, rot, rng, rng.randint(n // 3, n), 2)
    return V, rot


FAMS = {
    'tree_path': lambda n, r: tree_rot(n, r, 'path'),
    'tree_star': lambda n, r: tree_rot(n, r, 'star'),
    'tree_cater': lambda n, r: tree_rot(n, r, 'cater'),
    'tree_spider': lambda n, r: tree_rot(n, r, 'spider'),
    'tree_binary': lambda n, r: tree_rot(n, r, 'binary'),
    'tree_broom': lambda n, r: tree_rot(n, r, 'broom'),
    'tree_rand': lambda n, r: tree_rot(n, r, 'rand'),
    'tree_deep': lambda n, r: tree_rot(n, r, 'deep'),
    'loc_few': lambda n, r: (lambda V_rot: (V_rot[0], local_chords(V_rot[0], V_rot[1], r, r.randint(1, max(1, n // 4)), 3)))(tree_rot(n, r, r.choice(['rand', 'deep', 'cater', 'spider']))),
    'loc_many': lambda n, r: (lambda V_rot: (V_rot[0], local_chords(V_rot[0], V_rot[1], r, r.randint(n // 2, 2 * n), r.choice([2, 3, 4, 6]))))(tree_rot(n, r, r.choice(['rand', 'deep', 'cater', 'spider', 'binary']))),
    'any_few': lambda n, r: (lambda V_rot: (V_rot[0], any_chords(V_rot[0], V_rot[1], r, r.randint(1, 3))))(tree_rot(n, r, r.choice(['rand', 'deep', 'path']))),
    'wheel': wheel,
    'nested': nested,
    'cactus': cactus,
    'sibling': sibling_fan,
    'hub': hub_face,
    'strip': tri_strip,
    'onion': onion,
    'ears': ears,
}
