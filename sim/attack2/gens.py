"""Plane graph generators for attack2 (rotation systems, mostly combinatorial).

Conventions of rot.Plane: rot[v] ccw list of edge ids; corner (v, j) between rot[v][j-1] and rot[v][j],
lying on the face of the outgoing dart (v, rot[v][j-1]).
"""
import sys, os, math, random, itertools
import numpy as np, networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'attack'))
sys.path.insert(0, os.path.join(HERE, '..', 'tiles'))
from rot import Plane
from scipy.spatial import Delaunay


def euler_ok(P):
    V, E, F = P.euler()
    return V - E + F == 2 and P.components() == 1


def adj_sets(P):
    adj = {v: set() for v in P.rot}
    for e, (a, b) in P.edges.items():
        adj[a].add(b); adj[b].add(a)
    return adj


def new_vertex(P):
    v = max(P.rot) + 1 if P.rot else 0
    P.rot[v] = []
    return v


def add_edge_at(P, x, ix, y, iy):
    """insert edge x-y at rotation positions ix (in rot[x]) and iy (in rot[y])."""
    e = P.new_eid(); P.edges[e] = (x, y)
    P.rot[x].insert(ix, e)
    P.rot[y].insert(iy, e)
    return e


def chord_in_face(P, rng, adj, big_bias=1.0, tries=60):
    """add one edge inside a face between two corners of distinct, non-adjacent vertices."""
    faces, df = P.faces()
    wts = [len(f) ** big_bias if len(f) >= 3 else 0 for f in faces]
    if sum(wts) == 0:
        return False
    for _ in range(tries):
        f = rng.choices(range(len(faces)), weights=wts)[0]
        cyc = faces[f]
        i, k = rng.sample(range(len(cyc)), 2)
        (x, ex), (y, ey) = cyc[i], cyc[k]
        if x == y or y in adj[x]:
            continue
        ix = P.rot[x].index(ex) + 1
        iy = P.rot[y].index(ey) + 1
        add_edge_at(P, x, ix, y, iy)
        adj[x].add(y); adj[y].add(x)
        return True
    return False


def tree_plus(n, extra, rng, attach='uniform', big_bias=1.0):
    """random plane tree (random rotations) + `extra` chords drawn in faces."""
    P = Plane()
    P.rot[0] = []
    for i in range(1, n):
        if attach == 'uniform':
            p = rng.randrange(i)
        elif attach == 'path':
            p = i - 1 if rng.random() < 0.8 else rng.randrange(i)
        elif attach == 'star':
            p = 0 if rng.random() < 0.3 else rng.randrange(i)
        elif attach == 'pref':
            # preferential attachment by degree
            degs = [len(P.rot[v]) + 1 for v in range(i)]
            p = rng.choices(range(i), weights=degs)[0]
        else:
            raise ValueError(attach)
        P.rot[i] = []
        e = P.new_eid(); P.edges[e] = (p, i)
        P.rot[p].insert(rng.randrange(len(P.rot[p]) + 1), e)
        P.rot[i].append(e)
    adj = adj_sets(P)
    for _ in range(extra):
        chord_in_face(P, rng, adj, big_bias)
    assert euler_ok(P)
    return P


def delaunay(n, drop, rng):
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    tri = Delaunay(pts)
    E = set()
    for s in tri.simplices:
        for a, b in itertools.combinations(sorted(s), 2):
            E.add((int(a), int(b)))
    E = sorted(E)
    G = nx.Graph(E)
    for idx in rng.sample(range(len(E)), len(E)):
        a, b = E[idx]
        if rng.random() < drop:
            G.remove_edge(a, b)
            if not nx.is_connected(G):
                G.add_edge(a, b)
    pos = {i: tuple(pts[i]) for i in range(n)}
    P = Plane.from_coords(pos, sorted(G.edges()))
    assert euler_ok(P)
    return P


def grid(a, b, rng, drop=0.0, diag=0.0):
    pos = {}; E = []
    vid = lambda i, j: i * b + j
    for i in range(a):
        for j in range(b):
            pos[vid(i, j)] = (i + 1e-6 * rng.random(), j + 1e-6 * rng.random())
            if i + 1 < a: E.append((vid(i, j), vid(i + 1, j)))
            if j + 1 < b: E.append((vid(i, j), vid(i, j + 1)))
            if i + 1 < a and j + 1 < b and rng.random() < diag:
                E.append((vid(i, j), vid(i + 1, j + 1)) if rng.random() < .5 else (vid(i + 1, j), vid(i, j + 1)))
    G = nx.Graph(E)
    for e in rng.sample(E, len(E)):
        if rng.random() < drop:
            G.remove_edge(*e)
            if not nx.is_connected(G):
                G.add_edge(*e)
    P = Plane.from_coords(pos, sorted(G.edges()))
    assert euler_ok(P)
    return P


def nested_cycles(rings, m, rng, spoke=0.5, drop=0.0, hub=True):
    """concentric cycles (long faces), random spokes, optional central hub joined to ring 0."""
    pos = {}; E = []
    vid = lambda r, j: r * m + j
    for r in range(rings):
        rad = 1 + r
        for j in range(m):
            th = 2 * math.pi * j / m + 0.01 * r
            pos[vid(r, j)] = (rad * math.cos(th), rad * math.sin(th))
            E.append((vid(r, j), vid(r, (j + 1) % m)))
            if r + 1 < rings and rng.random() < spoke:
                E.append((vid(r, j), vid(r + 1, j)))
    for r in range(rings - 1):          # keep connected
        j = rng.randrange(m)
        E.append((vid(r, j), vid(r + 1, j)))
    if hub:
        c = rings * m
        pos[c] = (0.0, 0.0)
        for j in range(m):
            E.append((c, vid(0, j)))
    E = sorted(set(tuple(sorted(e)) for e in E))
    G = nx.Graph(E)
    for e in rng.sample(E, len(E)):
        if rng.random() < drop:
            G.remove_edge(*e)
            if not nx.is_connected(G):
                G.add_edge(*e)
    P = Plane.from_coords(pos, sorted(G.edges()))
    assert euler_ok(P)
    return P


def multi_wheel(k, m, rng, rimdrop=0.0):
    """k x k grid of cells; every cell gets a hub joined to all its m boundary points (fans/wheels)."""
    # build a grid of (k*(m//4)+1) points per side, hub in each cell joined to its boundary
    s = max(1, m // 4)
    side = k * s + 1
    pos = {}; E = []
    vid = lambda i, j: i * side + j
    onb = lambda i, j: i % s == 0 or j % s == 0
    for i in range(side):
        for j in range(side):
            if not onb(i, j):
                continue
            pos[vid(i, j)] = (i, j)
            if i + 1 < side and j % s == 0: E.append((vid(i, j), vid(i + 1, j)))
            if j + 1 < side and i % s == 0: E.append((vid(i, j), vid(i, j + 1)))
    nxt = side * side
    for ci in range(k):
        for cj in range(k):
            h = nxt; nxt += 1
            pos[h] = (ci * s + s / 2 + 0.01, cj * s + s / 2 - 0.01)
            bd = set()
            for t in range(s + 1):
                bd |= {vid(ci * s + t, cj * s), vid(ci * s + t, cj * s + s), vid(ci * s, cj * s + t), vid(ci * s + s, cj * s + t)}
            for x in bd:
                E.append((h, x))
    E = sorted(set(tuple(sorted(e)) for e in E))
    G = nx.Graph(E)
    for e in rng.sample(E, len(E)):
        a, b = e
        if a < side * side and b < side * side and rng.random() < rimdrop:
            G.remove_edge(*e)
            if not nx.is_connected(G):
                G.add_edge(*e)
    P = Plane.from_coords(pos, sorted(G.edges()))
    assert euler_ok(P)
    return P


def outerplanar(n, chords, rng, pendants=0):
    """points on a circle, random non-crossing straight chords, then pendant leaves/paths."""
    pos = {i: (math.cos(2 * math.pi * i / n), math.sin(2 * math.pi * i / n)) for i in range(n)}
    E = [(i, (i + 1) % n) for i in range(n)]
    ch = []
    def cross(a, b, c, d):
        a, b = sorted((a, b)); c, d = sorted((c, d))
        if len({a, b, c, d}) < 4:
            return False
        return (a < c < b) != (a < d < b)
    for _ in range(chords * 10):
        if len(ch) >= chords:
            break
        a, b = rng.sample(range(n), 2)
        if abs(a - b) in (1, n - 1):
            continue
        if any(cross(a, b, c, d) for c, d in ch) or (min(a, b), max(a, b)) in ch:
            continue
        ch.append((min(a, b), max(a, b)))
    P = Plane.from_coords(pos, sorted(set(tuple(sorted(e)) for e in E + ch)))
    for _ in range(pendants):
        x = rng.choice(list(P.rot))
        v = new_vertex(P)
        add_edge_at(P, x, rng.randrange(len(P.rot[x]) + 1), v, 0)
    assert euler_ok(P)
    return P


def cactus(n_cycles, rng, cmin=3, cmax=7, pendants=0, hub_bias=0.0):
    """cycles glued at single vertices (many cut vertices, pinches); hub_bias>0 glues many at one vertex."""
    P = Plane()
    P.rot[0] = []
    first = True
    for _ in range(n_cycles):
        if first:
            x = 0
        elif rng.random() < hub_bias:
            x = 0
        else:
            x = rng.choice(list(P.rot))
        L = rng.randint(cmin, cmax)
        vs = [x] + [new_vertex(P) for _ in range(L - 1)]
        pos = rng.randrange(len(P.rot[x]) + 1)
        es = []
        for i in range(L):
            a, b = vs[i], vs[(i + 1) % L]
            e = P.new_eid(); P.edges[e] = (a, b); es.append(e)
        # rotation: at x the two cycle edges inserted consecutively; others degree 2
        P.rot[x][pos:pos] = [es[0], es[-1]]
        for i in range(1, L):
            P.rot[vs[i]] = [es[i - 1], es[i]]
        first = False
    for _ in range(pendants):
        x = rng.choice(list(P.rot))
        v = new_vertex(P)
        add_edge_at(P, x, rng.randrange(len(P.rot[x]) + 1), v, 0)
    if not euler_ok(P):
        # fix orientation at x if needed: try reversing pairs (should not happen)
        raise AssertionError('cactus not plane')
    return P


def set_weights(P, rng, mode='small'):
    for e in P.edges:
        for di in (0, 1):
            if mode == 'small':
                w = rng.randint(1, 19)
            elif mode == 'unit':
                w = 1
            elif mode == 'heavy':
                w = int(10 ** rng.uniform(0, 6))
            elif mode == 'asym':
                w = 1 if di == 0 else rng.choice([1, 1000])
            elif mode == 'binary':
                w = rng.choice([1, 2])
            else:
                raise ValueError(mode)
            P.w[(e, di)] = w
    return P


FAMILIES = {
    'treeplus_sparse': lambda rng: tree_plus(rng.randint(40, 160), rng.randint(0, 12), rng, rng.choice(['uniform', 'path', 'pref', 'star'])),
    'treeplus_mid': lambda rng: tree_plus(rng.randint(40, 160), rng.randint(20, 80), rng, rng.choice(['uniform', 'path', 'pref', 'star'])),
    'treeplus_dense': lambda rng: tree_plus(rng.randint(40, 140), rng.randint(80, 250), rng, rng.choice(['uniform', 'pref']), big_bias=2.0),
    'delaunay': lambda rng: delaunay(rng.randint(40, 160), rng.choice([0.0, 0.2, 0.4, 0.6]), rng),
    'grid': lambda rng: grid(rng.randint(4, 14), rng.randint(4, 14), rng, drop=rng.choice([0, 0.1, 0.3]), diag=rng.choice([0, 0.3, 1.0])),
    'nested': lambda rng: nested_cycles(rng.randint(2, 6), rng.randint(6, 24), rng, spoke=rng.choice([0.1, 0.3, 0.8]), drop=rng.choice([0, 0.2]), hub=rng.random() < 0.6),
    'wheels': lambda rng: multi_wheel(rng.randint(1, 4), rng.choice([4, 8, 12, 16]), rng, rimdrop=rng.choice([0, 0.3])),
    'outerplanar': lambda rng: outerplanar(rng.randint(12, 80), rng.randint(0, 40), rng, pendants=rng.randint(0, 30)),
    'cactus': lambda rng: cactus(rng.randint(3, 25), rng, pendants=rng.randint(0, 15), hub_bias=rng.choice([0, 0.3, 0.7])),
}


def star_g(m, rng):
    pos = {0: (0.0, 0.0)}
    pos.update({i + 1: (math.cos(2 * math.pi * i / m), math.sin(2 * math.pi * i / m)) for i in range(m)})
    return Plane.from_coords(pos, [(0, i + 1) for i in range(m)])


def windmill_g(m, rng):
    pos = {0: (0.0, 0.0)}; E = []
    for i in range(m):
        a, b = 2 * math.pi * (i + 0.15) / m, 2 * math.pi * (i + 0.85) / m
        pos[2 * i + 1] = (math.cos(a), math.sin(a)); pos[2 * i + 2] = (math.cos(b), math.sin(b))
        E += [(0, 2 * i + 1), (0, 2 * i + 2), (2 * i + 1, 2 * i + 2)]
    return Plane.from_coords(pos, E)


def k2m_g(m, rng):
    pos = {0: (0.0, 1.0), 1: (0.0, -1.0)}
    pos.update({i + 2: (i - (m - 1) / 2.0, 0.0) for i in range(m)})
    return Plane.from_coords(pos, [(0, i + 2) for i in range(m)] + [(1, i + 2) for i in range(m)])


def fan_g(m, rng):
    """path 1..m plus hub 0 adjacent to all (fan), plus random pendants."""
    pos = {0: (0.0, 5.0)}
    pos.update({i: (float(i), 0.0) for i in range(1, m + 1)})
    E = [(0, i) for i in range(1, m + 1)] + [(i, i + 1) for i in range(1, m)]
    P = Plane.from_coords(pos, E)
    for _ in range(rng.randint(0, m)):
        x = rng.choice(list(P.rot)); v = new_vertex(P)
        add_edge_at(P, x, rng.randrange(len(P.rot[x]) + 1), v, 0)
    return P


def broom_g(m, rng):
    """long path with a cluster of m pendants (and a few triangles) at one vertex."""
    P = tree_plus(rng.randint(5, 30), 0, rng, 'path')
    h = rng.choice(list(P.rot))
    for _ in range(m):
        v = new_vertex(P)
        add_edge_at(P, h, rng.randrange(len(P.rot[h]) + 1), v, 0)
    adj = adj_sets(P)
    for _ in range(rng.randint(0, m // 2)):
        chord_in_face(P, rng, adj)
    assert euler_ok(P)
    return P


FAMILIES.update({
    'tiny': lambda rng: tree_plus(rng.randint(3, 9), rng.randint(0, 10), rng, rng.choice(['uniform', 'path', 'pref', 'star'])),
    'star': lambda rng: star_g(rng.randint(4, 60), rng),
    'windmill': lambda rng: windmill_g(rng.randint(2, 25), rng),
    'k2m': lambda rng: k2m_g(rng.randint(3, 40), rng),
    'fan': lambda rng: fan_g(rng.randint(3, 40), rng),
    'broom': lambda rng: broom_g(rng.randint(3, 40), rng),
})
