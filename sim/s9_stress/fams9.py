"""adv9: new straight-line plane families meant to stress Lemmas B2-B4 (holes, pinches, hubs, long paths)."""
import math, random, itertools
import numpy as np, networkx as nx
from geo import _delaunay_edges, keep_connected_drop, fam_del
from core import seg_cross


def _largest(pos, E):
    G = nx.Graph(); G.add_nodes_from(range(len(pos))); G.add_edges_from(E)
    keep = sorted(max(nx.connected_components(G), key=len))
    idx = {v: i for i, v in enumerate(keep)}
    pos2 = np.array([pos[v] for v in keep], float)
    E2 = sorted(set((min(idx[a], idx[b]), max(idx[a], idx[b])) for a, b in E if a in idx and b in idx))
    return pos2, E2


def _noncrossing(pos, E):
    pos = np.asarray(pos, float); out = []
    for a, b in E:
        key = (min(a, b), max(a, b))
        if a == b or key in out:
            continue
        if out:
            PA = pos[[x for x, y in out]]; PB = pos[[y for x, y in out]]
            if seg_cross(pos[a], pos[b], PA, PB):
                continue
        out.append(key)
    return out


def fam_swiss(n, k, rad, drop, seed):
    """Delaunay with k random disks of vertices removed (big faces) and some edges dropped."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = r.random((n, 2))
    cs = r.random((k, 2)); rr = r.uniform(0.3, 1.0, k) * rad
    keep = [i for i in range(n) if all(np.linalg.norm(pos[i] - cs[j]) > rr[j] for j in range(k))]
    pos = pos[keep]
    E = _delaunay_edges(pos)
    # remove Delaunay edges that pass through a removed disk (makes the holes real faces)
    E2 = []
    for a, b in E:
        mid = (pos[a] + pos[b]) / 2
        if any(np.linalg.norm(mid - cs[j]) < rr[j] for j in range(k)):
            continue
        E2.append((a, b))
    pos, E2 = _largest(pos, E2)
    E2 = keep_connected_drop(len(pos), E2, drop, rng)
    return pos, E2


def fam_dlsparse(n, drop, seed):
    return fam_del(n, drop, seed)


def fam_ringch(R, K, p, q, seed):
    """nested rings, sparse radial spokes (prob p), diagonal chords in annuli (prob q), centre hub."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, 0.0)]
    for i in range(1, R + 1):
        for j in range(K):
            a = 2 * math.pi * j / K + r.uniform(-0.03, 0.03) + 0.37 * i
            pos.append((i * math.cos(a), i * math.sin(a)))
    vid = lambda i, j: 1 + (i - 1) * K + (j % K)
    E = []
    for i in range(1, R + 1):
        for j in range(K):
            if rng.random() < 0.93 or i == R:
                E.append((vid(i, j), vid(i, j + 1)))
            if i == 1:
                if rng.random() < p or j == 0:
                    E.append((0, vid(1, j)))
            else:
                if rng.random() < p or j == 0:
                    E.append((vid(i - 1, j), vid(i, j)))
                if rng.random() < q:
                    E.append((vid(i - 1, j), vid(i, j + 1)))
                if rng.random() < q / 2:
                    E.append((vid(i - 1, j + 1), vid(i, j)))
    E = _noncrossing(pos, E)
    return _largest(pos, E)


def fam_k2mh(h, m, sub, pchain, seed):
    """stack of K_{2,m}'s: hubs H_0..H_h on the y-axis; between H_j and H_{j+1} m petals (paths of
    sub vertices) on both sides; petal vertices of one level joined in a chain with prob pchain;
    hub-hub chords.  Many high-degree vertices that sit on many separators."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, 2.0 * j) for j in range(h + 1)]
    E = [(j, j + 1) for j in range(h)]
    for j in range(h):
        side = []
        for i in list(range(-(m // 2), 0)) + list(range(1, m - m // 2 + 1)):
            ids = []
            for t in range(sub):
                y = 2 * j + 1 + (0 if sub == 1 else 0.7 - 1.4 * t / (sub - 1))
                pos.append((0.5 * i + r.uniform(-1e-3, 1e-3), y + r.uniform(-1e-3, 1e-3)))
                ids.append(len(pos) - 1)
            E.append((j + 1, ids[0])); E.append((ids[-1], j))
            E += list(zip(ids, ids[1:]))
            side.append((i, ids))
        side.sort()
        for (i1, a), (i2, b) in zip(side, side[1:]):
            if i1 * i2 > 0 and rng.random() < pchain:
                t = rng.randrange(len(a))
                E.append((a[t], b[t]))
    E = _noncrossing(pos, E)
    return _largest(pos, E)


def fam_cactus(n, extra, chordp, seed):
    """geometric tree whose edges are blown up into thin diamonds a-p-b-p'-a (so tree vertices are pinch
    vertices of high degree), optional chord ab inside each diamond, plus a few extra edges."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pts = r.random((n, 2))
    E0 = _delaunay_edges(pts)
    G = nx.Graph(); G.add_weighted_edges_from((a, b, rng.random()) for a, b in E0)
    T = nx.minimum_spanning_tree(G)
    pos = [tuple(p) for p in pts]; E = []
    for a, b in T.edges():
        P0, P1 = np.array(pos[a]), np.array(pos[b]); d = P1 - P0; L = np.linalg.norm(d)
        nrm = np.array([-d[1], d[0]]) / L
        mid = (P0 + P1) / 2
        w = 0.12 * L
        pos.append(tuple(mid + w * nrm)); p1 = len(pos) - 1
        pos.append(tuple(mid - w * nrm)); p2 = len(pos) - 1
        E += [(a, p1), (p1, b), (b, p2), (p2, a)]
        if rng.random() < chordp:
            E.append((a, b))
    Tset = set((min(a, b), max(a, b)) for a, b in T.edges())
    others = [e for e in E0 if e not in Tset]
    rng.shuffle(others)
    E = _noncrossing(pos, E)
    E = _noncrossing(pos, E + others[:extra])
    return _largest(pos, E)


def fam_subdl(n, drop, sub, seed):
    """Delaunay with every edge subdivided into sub+1 pieces (long degree-2 paths)."""
    pos, E = fam_del(n, drop, seed)
    pos = [tuple(p) for p in pos]; E2 = []
    rng = random.Random(seed)
    for a, b in E:
        k = rng.randint(0, sub)
        prev = a
        for t in range(1, k + 1):
            pa, pb = np.array(pos[a]), np.array(pos[b])
            pos.append(tuple(pa + (pb - pa) * t / (k + 1))); cur = len(pos) - 1
            E2.append((prev, cur)); prev = cur
        E2.append((prev, b))
    return np.array(pos), sorted(set((min(a, b), max(a, b)) for a, b in E2))


def fam_gridholes(k, nh, hs, diag, seed):
    """k x k grid with nh rectangular holes (interior vertices removed) and random diagonals."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    removed = set()
    for _ in range(nh):
        w = rng.randint(2, hs); h = rng.randint(2, hs)
        x0 = rng.randrange(0, max(1, k - w)); y0 = rng.randrange(0, max(1, k - h))
        for i in range(x0 + 1, x0 + w):
            for j in range(y0 + 1, y0 + h):
                removed.add((i, j))
    vid = {}; pos = []
    for i in range(k):
        for j in range(k):
            if (i, j) not in removed:
                vid[(i, j)] = len(pos); pos.append((i + r.uniform(-0.1, 0.1), j + r.uniform(-0.1, 0.1)))
    E = []
    for (i, j), v in vid.items():
        for di, dj in ((1, 0), (0, 1)):
            if (i + di, j + dj) in vid:
                E.append((v, vid[(i + di, j + dj)]))
        if rng.random() < diag and (i + 1, j + 1) in vid and (i + 1, j) in vid and (i, j + 1) in vid:
            if rng.random() < 0.5:
                E.append((v, vid[(i + 1, j + 1)]))
            else:
                E.append((vid[(i + 1, j)], vid[(i, j + 1)]))
    pos, E = _largest(pos, [(min(a, b), max(a, b)) for a, b in E])
    return pos, E


def fam_spiral(turns, per, p, seed):
    """Archimedean spiral path with radial chords between consecutive turns (prob p): long thin strips."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    N = turns * per
    pos = []
    for t in range(N):
        th = 2 * math.pi * t / per
        rad = 1.0 + th / (2 * math.pi)
        pos.append((rad * math.cos(th) + r.uniform(-1e-3, 1e-3), rad * math.sin(th) + r.uniform(-1e-3, 1e-3)))
    E = [(t, t + 1) for t in range(N - 1)]
    for t in range(N - per):
        if rng.random() < p:
            E.append((t, t + per))
        if rng.random() < p / 3:
            E.append((t, t + per + 1))
    pos.append((0.0, 0.0))
    for t in range(per):
        if rng.random() < 0.5 or t == 0:
            E.append((N, t))
    E = _noncrossing(pos, E)
    return _largest(pos, E)


def fam_wheels(k, m, p, seed):
    """big wheel whose rim vertices are hubs of small wheels (hubs of degree m+..); wheels share rim
    vertices sparsely -> vertices on many separators, pinches between small wheels."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, 0.0)]; E = []
    hubs = []
    for i in range(k):
        a = 2 * math.pi * i / k
        pos.append((10 * math.cos(a), 10 * math.sin(a))); hubs.append(len(pos) - 1)
        E.append((0, len(pos) - 1))
    for i in range(k):
        E.append((hubs[i], hubs[(i + 1) % k]))
    rad = 10 * math.sin(math.pi / k) * 0.45
    for i, h in enumerate(hubs):
        c = np.array(pos[h]); rim = []
        for j in range(m):
            a = 2 * math.pi * j / m + r.uniform(-0.02, 0.02)
            pos.append(tuple(c + rad * np.array([math.cos(a), math.sin(a)]))); rim.append(len(pos) - 1)
            if rng.random() < p or j == 0:
                E.append((h, rim[-1]))
        for j in range(m):
            if rng.random() < 0.85:
                E.append((rim[j], rim[(j + 1) % m]))
    E = _noncrossing(pos, E)
    return _largest(pos, E)


FAMS9 = dict(
    swiss=lambda s, a: fam_swiss(a['n'], a['k'], a['rad'], a['drop'], s),
    dlsparse=lambda s, a: fam_dlsparse(a['n'], a['drop'], s),
    ringch=lambda s, a: fam_ringch(a['R'], a['K'], a['p'], a['q'], s),
    k2mh=lambda s, a: fam_k2mh(a['h'], a['m'], a['sub'], a['pc'], s),
    cactus=lambda s, a: fam_cactus(a['n'], a['extra'], a['chord'], s),
    subdl=lambda s, a: fam_subdl(a['n'], a['drop'], a['sub'], s),
    gridholes=lambda s, a: fam_gridholes(a['k'], a['nh'], a['hs'], a['diag'], s),
    spiral=lambda s, a: fam_spiral(a['turns'], a['per'], a['p'], s),
    wheels=lambda s, a: fam_wheels(a['k'], a['m'], a['p'], s),
)


def params9(fam, r, scale=1.0):
    S = lambda lo, hi: int(r.randint(int(lo * scale), max(int(lo * scale), int(hi * scale))))
    if fam == 'swiss': return dict(n=S(120, 400), k=r.randint(3, 12), rad=r.choice([0.08, 0.12, 0.18]), drop=r.choice([0.0, 0.2, 0.4]))
    if fam == 'dlsparse': return dict(n=S(80, 300), drop=r.choice([0.6, 0.75, 0.85]))
    if fam == 'ringch': return dict(R=r.randint(4, 9), K=S(10, 30), p=r.choice([0.1, 0.2, 0.35]), q=r.choice([0.1, 0.3, 0.6]))
    if fam == 'k2mh': return dict(h=r.randint(2, 5), m=S(8, 30), sub=r.choice([1, 1, 2, 3]), pc=r.choice([0.0, 0.3, 0.7]))
    if fam == 'cactus': return dict(n=S(30, 110), extra=r.randint(0, 30), chord=r.choice([0.0, 0.3, 0.8]))
    if fam == 'subdl': return dict(n=S(30, 90), drop=r.choice([0.0, 0.3, 0.5]), sub=r.choice([2, 3, 5]))
    if fam == 'gridholes': return dict(k=S(10, 22), nh=r.randint(2, 10), hs=r.randint(3, 6), diag=r.choice([0.0, 0.3, 0.7]))
    if fam == 'spiral': return dict(turns=r.randint(3, 8), per=S(10, 30), p=r.choice([0.15, 0.3, 0.6]))
    if fam == 'wheels': return dict(k=r.randint(5, 12), m=S(6, 20), p=r.choice([0.3, 0.6, 1.0]))
    raise KeyError(fam)
