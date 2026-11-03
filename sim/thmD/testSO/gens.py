"""Extra instance generators (rotation systems in the driver's Builder format) aimed at long P,
deep recursion and many equal-length shortest paths. No loops (GHAT_REPAIR.md deletes them)."""
import random
import networkx as nx
import adv

T = adv.T
Builder = T.Builder


def strip(rng):
    """long grid strip a x L with s at one end and t at the other: P runs along the strip."""
    a, L = rng.randint(2, 4), rng.randint(8, 30)
    G = nx.grid_2d_graph(a, L)
    used = set()
    for _ in range(rng.randint(0, L // 2)):
        r, c = rng.randrange(a - 1), rng.randrange(L - 1)
        if (r, c) in used:
            continue
        used.add((r, c))
        if rng.random() < 0.5:
            G.add_edge((r, c), (r + 1, c + 1))
        else:
            G.add_edge((r + 1, c), (r, c + 1))
    nodes = list(G.nodes())
    B = Builder.from_nx(G)
    s = nodes.index((rng.randrange(a), 0))
    t = nodes.index((rng.randrange(a), L - 1))
    return B, s, t


def cyl(rng):
    """concentric rings with spokes, a hub vertex, s and t at the hub and on the outer ring."""
    k, L = rng.randint(3, 10), rng.randint(3, 8)
    G = nx.Graph()
    for r in range(k):
        for i in range(L):
            G.add_edge((r, i), (r, (i + 1) % L))
    for r in range(k - 1):
        for i in range(L):
            if rng.random() < 0.6 or i == 0:
                G.add_edge((r, i), (r + 1, (i + rng.choice([0, 0, 1])) % L))
    G.add_node('c')
    for i in range(L):
        if rng.random() < 0.7 or i == 0:
            G.add_edge('c', (0, i))
    nodes = list(G.nodes())
    B = Builder.from_nx(G)
    s = nodes.index('c')
    t = nodes.index((k - 1, rng.randrange(L)))
    if rng.random() < 0.5:
        s, t = t, s
    return B, s, t


def tri(rng):
    """Delaunay triangulation (some edges removed), s and t far apart."""
    import numpy as np
    from scipy.spatial import Delaunay
    n = rng.randint(10, 60)
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    tr = Delaunay(pts)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for simp in tr.simplices:
        a, b, c = map(int, simp)
        G.add_edges_from([(a, b), (b, c), (a, c)])
    B = Builder.from_nx(G)
    B = T.remove_some(B, rng, rng.uniform(0.0, 0.3))
    s = min(range(n), key=lambda v: pts[v][0])
    t = max(range(n), key=lambda v: pts[v][0])
    return B, s, t


def decorate(B, rng):
    """parallel edges, subdivisions, pendants (bridges)."""
    for _ in range(rng.choice([0, 0, 1, 2, 4])):
        B.add_parallel(rng.randrange(len(B.ends)))
    for _ in range(rng.choice([0, 0, 1, 3])):
        B.subdivide(rng.randrange(len(B.ends)))
    for _ in range(rng.choice([0, 0, 1, 2])):
        B.add_pendant(rng.randrange(B.n), rng)
    return B


def caps_for(m, rng):
    sc = rng.choice(['one', 'one', 'z01', 'r12', 'r123', 'zero_some', 'big_some'])
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
    return sc, [rng.choice([1, 1, 1, 2, 50]) for _ in range(m)]


def longstrip(rng):
    """a x L strip with L in [40, 90]: long P, recursion depth 7 and more."""
    a, L = rng.choice([2, 2, 3]), rng.randint(40, 90)
    G = nx.grid_2d_graph(a, L)
    used = set()
    for _ in range(rng.randint(0, L // 3)):
        r, c = rng.randrange(a - 1), rng.randrange(L - 1)
        if (r, c) in used:
            continue
        used.add((r, c))
        if rng.random() < 0.5:
            G.add_edge((r, c), (r + 1, c + 1))
        else:
            G.add_edge((r + 1, c), (r, c + 1))
    nodes = list(G.nodes())
    B = Builder.from_nx(G)
    return B, nodes.index((rng.randrange(a), 0)), nodes.index((rng.randrange(a), L - 1))


GENS = {'strip': strip, 'cyl': cyl, 'tri': tri, 'longstrip': longstrip}


def make(seed, fam=None):
    for k in range(20):
        try:
            return _make(seed if k == 0 else seed + 1000003 * k, fam)
        except AssertionError:
            continue
    raise RuntimeError('generator failed')


def _make(seed, fam=None):
    rng = random.Random(seed)
    fam = fam or rng.choice(['strip', 'strip', 'cyl', 'cyl', 'tri', 'driver'])
    if fam == 'driver':
        T.SIZE_MAX, T.GRID_MAX = 60, 12
        I = T.make_instance(seed)
        sc, cap = caps_for(len(I['ends']), rng)
        if rng.random() < 0.5:
            I['cap'] = cap
            I['scheme'] = sc
        I['family'] = 'driver_' + I['family']
        return I
    B, s, t = GENS[fam](rng)
    if rng.random() < 0.4:
        B = decorate(B, rng)
    assert B.connected() and B.euler_ok()
    sc, cap = caps_for(len(B.ends), rng)
    return dict(seed=seed, family=fam, scheme=sc, n=B.n, ends=list(B.ends), rot=B.rot, cap=cap, s=s, t=t)
