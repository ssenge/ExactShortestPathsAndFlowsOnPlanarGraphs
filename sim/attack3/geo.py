"""Straight-line plane graph families + virtual-edge candidates (segments crossing no edge of G)."""
import math, itertools, random
import numpy as np, networkx as nx
from scipy.spatial import Delaunay
from core import seg_cross


def _delaunay_edges(pts):
    tri = Delaunay(pts)
    E = set()
    for s in tri.simplices:
        for a, b in itertools.combinations(sorted(s), 2):
            E.add((int(a), int(b)))
    return sorted(E)


def virtual_candidates(pos, edges, extra_pairs=()):
    pos = np.asarray(pos, float)
    Es = set((min(a, b), max(a, b)) for a, b in edges)
    A = np.array([pos[a] for a, b in edges]); B = np.array([pos[b] for a, b in edges])
    cand = set(_delaunay_edges(pos)) | set((min(a, b), max(a, b)) for a, b in extra_pairs)
    out = set()
    for a, b in cand:
        if (a, b) in Es:
            continue
        # proper crossing with an edge of G, or passing through a vertex
        if seg_cross(pos[a], pos[b], A, B):
            continue
        d = pos[b] - pos[a]; L2 = d @ d
        t = ((pos - pos[a]) @ d) / L2
        proj = pos[a] + np.outer(t, d)
        dist = np.linalg.norm(pos - proj, axis=1)
        mask = (t > 1e-9) & (t < 1 - 1e-9) & (dist < 1e-9)
        if mask.any():
            continue
        out.add((a, b))
    return out


def keep_connected_drop(n, E, drop, rng):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    order = list(E); rng.shuffle(order)
    for a, b in order:
        if rng.random() < drop:
            G.remove_edge(a, b)
            if not nx.is_connected(G):
                G.add_edge(a, b)
    return sorted((min(a, b), max(a, b)) for a, b in G.edges())


def fam_del(n, drop, seed):
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = r.random((n, 2))
    E = keep_connected_drop(n, _delaunay_edges(pos), drop, rng)
    return pos, E


def fam_grid(k, drop, seed):
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = []
    for i in range(k):
        for j in range(k):
            pos.append((i + r.uniform(-0.15, 0.15), j + r.uniform(-0.15, 0.15)))
    pos = np.array(pos)
    E = []
    vid = lambda i, j: i * k + j
    for i in range(k):
        for j in range(k):
            if i + 1 < k: E.append((vid(i, j), vid(i + 1, j)))
            if j + 1 < k: E.append((vid(i, j), vid(i, j + 1)))
            if i + 1 < k and j + 1 < k and rng.random() < 0.5:
                if rng.random() < 0.5: E.append((vid(i, j), vid(i + 1, j + 1)))
                else: E.append((vid(i + 1, j), vid(i, j + 1)))
    E = keep_connected_drop(len(pos), [(min(a, b), max(a, b)) for a, b in E], drop, rng)
    return pos, E


def fam_k2m(m, chord=True, sub=1, seed=0):
    """K_{2,m} (petals of length sub+1) plus the chord uw; u=(0,1), w=(0,-1)."""
    r = np.random.default_rng(seed)
    pos = [(0.0, 1.0), (0.0, -1.0)]
    E = []
    for i in range(1, m + 1):
        ids = []
        for t in range(sub):
            y = 0.0 if sub == 1 else (0.6 - 1.2 * t / (sub - 1))
            pos.append((float(i) + r.uniform(-1e-3, 1e-3), y + r.uniform(-1e-3, 1e-3)))
            ids.append(len(pos) - 1)
        E.append((0, ids[0])); E.append((ids[-1], 1))
        for a, b in zip(ids, ids[1:]):
            E.append((a, b))
    if chord:
        E.append((0, 1))
    return np.array(pos), [(min(a, b), max(a, b)) for a, b in E]


def fam_fan(k, extra, seed):
    """apex + convex chain (fan), plus chords on the far side and random interior points."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, -3.0)]
    for i in range(k):
        t = -1 + 2 * i / (k - 1)
        pos.append((t * 3, 1.0 - t * t + r.uniform(-0.01, 0.01)))
    E = [(0, i) for i in range(1, k + 1)] + [(i, i + 1) for i in range(1, k)]
    # outer chords above the concave-down chain: arcs drawn as two-segment paths via new points
    for _ in range(extra):
        a = rng.randrange(1, k - 1); b = min(k, a + rng.randrange(2, 5))
        mid = ((pos[a][0] + pos[b][0]) / 2, max(pos[a][1], pos[b][1]) + 0.3 + rng.random())
        pos.append(mid); m_ = len(pos) - 1
        E += [(a, m_), (m_, b)]
    pos = np.array(pos)
    Es = set()
    out = []
    A = []
    for a, b in E:
        key = (min(a, b), max(a, b))
        if key in Es: continue
        PA = np.array([pos[x] for x, y in out]) if out else np.zeros((0, 2))
        PB = np.array([pos[y] for x, y in out]) if out else np.zeros((0, 2))
        if out and seg_cross(pos[a], pos[b], PA, PB):
            continue
        Es.add(key); out.append(key)
    G = nx.Graph(out)
    keep = max(nx.connected_components(G), key=len)
    idx = {v: i for i, v in enumerate(sorted(keep))}
    pos2 = np.array([pos[v] for v in sorted(keep)])
    E2 = [(idx[a], idx[b]) for a, b in out if a in keep and b in keep]
    return pos2, [(min(a, b), max(a, b)) for a, b in E2]


def fam_nested(R, K, p, seed):
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, 0.0)]
    for i in range(1, R + 1):
        for j in range(K):
            a = 2 * math.pi * j / K + r.uniform(-0.05, 0.05)
            pos.append((i * math.cos(a), i * math.sin(a)))
    vid = lambda i, j: 1 + (i - 1) * K + (j % K)
    E = []
    for i in range(1, R + 1):
        for j in range(K):
            if rng.random() < 0.9 or i == R:
                E.append((vid(i, j), vid(i, j + 1)))
            if i == 1:
                if rng.random() < p or j == 0: E.append((0, vid(1, j)))
            elif rng.random() < p or j == 0:
                E.append((vid(i - 1, j), vid(i, j)))
    E = [(min(a, b), max(a, b)) for a, b in E]
    G = nx.Graph(E)
    keep = max(nx.connected_components(G), key=len)
    idx = {v: i for i, v in enumerate(sorted(keep))}
    pos2 = np.array([pos[v] for v in sorted(keep)])
    return pos2, sorted(set((min(idx[a], idx[b]), max(idx[a], idx[b])) for a, b in E if a in keep))


def fam_pend(n, k, seed):
    """Delaunay on n points (30% dropped) plus k pendant leaves inside every corner."""
    pos, E = fam_del(n, 0.3, seed)
    pos = list(map(tuple, pos))
    adj = {v: [] for v in range(len(pos))}
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    E = list(E)
    for v in range(n):
        x, y = pos[v]
        angs = sorted(math.atan2(pos[u][1] - y, pos[u][0] - x) for u in adj[v])
        L = min(math.dist(pos[v], pos[u]) for u in adj[v]) * 0.2
        for (a_, b_) in E[:len(E)]:
            if v in (a_, b_) or a_ >= n or b_ >= n:
                continue
            P0 = np.array(pos[a_]); P1 = np.array(pos[b_]); V = np.array(pos[v])
            dd = P1 - P0; t = max(0.0, min(1.0, float((V - P0) @ dd / (dd @ dd))))
            L = min(L, 0.3 * float(np.linalg.norm(P0 + t * dd - V)))
        for i in range(len(angs)):
            a1 = angs[i]; a2 = angs[(i + 1) % len(angs)]
            span = (a2 - a1) % (2 * math.pi) or 2 * math.pi
            for t in range(k):
                a = a1 + span * (t + 1) / (k + 1)
                pos.append((x + L * math.cos(a), y + L * math.sin(a)))
                E.append((v, len(pos) - 1))
    return np.array(pos), [(min(a, b), max(a, b)) for a, b in E]


def fam_flower(k, L, seed):
    """centre c with k petals; petal = cycle c - p1 - ... - pL - c with a few inner chords and an
    inner vertex; petals share only c.  Plus a ring through petal tips (optional)."""
    rng = random.Random(seed); r = np.random.default_rng(seed)
    pos = [(0.0, 0.0)]; E = []
    for i in range(k):
        a0 = 2 * math.pi * i / k; a1 = 2 * math.pi * (i + 0.8) / k
        ids = []
        for t in range(L):
            rr = 1.0 + 2.0 * math.sin(math.pi * (t + 1) / (L + 1))
            a = a0 + (a1 - a0) * (t + 1) / (L + 1)
            pos.append((rr * math.cos(a), rr * math.sin(a))); ids.append(len(pos) - 1)
        E.append((0, ids[0])); E.append((0, ids[-1]))
        E += list(zip(ids, ids[1:]))
        # inner vertex joined to some petal vertices
        am = (a0 + a1) / 2
        pos.append((1.3 * math.cos(am), 1.3 * math.sin(am))); cvx = len(pos) - 1
        for t in ids:
            if rng.random() < 0.6: E.append((cvx, t))
        E.append((cvx, 0))
    if rng.random() < 0.5:   # ring through tips
        tips = [1 + i * (L + 1) + L // 2 for i in range(k)]
        for i in range(k):
            a, b = tips[i], tips[(i + 1) % k]
            E.append((a, b))
    pos = np.array(pos)
    out = []
    for a, b in E:
        key = (min(a, b), max(a, b))
        if key in out: continue
        if out:
            PA = np.array([pos[x] for x, y in out]); PB = np.array([pos[y] for x, y in out])
            if seg_cross(pos[a], pos[b], PA, PB):
                continue
        out.append(key)
    return pos, out


FAMS = dict(dl=lambda s, a: fam_del(a.get('n', 120), a.get('drop', 0.3), s),
            grid=lambda s, a: fam_grid(a.get('k', 10), a.get('drop', 0.2), s),
            k2m=lambda s, a: fam_k2m(a.get('m', 60), a.get('chord', True), a.get('sub', 1), s),
            fan=lambda s, a: fam_fan(a.get('k', 30), a.get('extra', 12), s),
            nested=lambda s, a: fam_nested(a.get('R', 5), a.get('K', 16), a.get('p', 0.35), s),
            pend=lambda s, a: fam_pend(a.get('n', 30), a.get('k', 3), s),
            flower=lambda s, a: fam_flower(a.get('k', 8), a.get('L', 6), s))


def drawing_ok(pos, E):
    pos = np.asarray(pos, float)
    A = np.array([pos[a] for a, b in E]); B = np.array([pos[b] for a, b in E])
    def orient(a, b, c):
        return (b[..., 0] - a[..., 0]) * (c[..., 1] - a[..., 1]) - (b[..., 1] - a[..., 1]) * (c[..., 0] - a[..., 0])
    for i in range(len(E)):
        o1 = orient(A[i], B[i], A); o2 = orient(A[i], B[i], B); o3 = orient(A, B, A[i]); o4 = orient(A, B, B[i])
        hit = (o1 * o2 < -1e-15) & (o3 * o4 < -1e-15)
        if hit.any():
            return False
    return True
