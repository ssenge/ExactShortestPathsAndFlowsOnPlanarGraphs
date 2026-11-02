"""Random and structured planar instances: Lemma N, the pipeline on the real N, with negative controls."""
import sys, os, random, collections, json, time, math
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import nlem

mode = sys.argv[1]
secs = float(sys.argv[2])
seed = int(sys.argv[3])
rng = random.Random(seed)
st = collections.Counter()
fails = []


def fail(msg, g, R):
    fails.append((msg, g.rot, R))
    if len(fails) < 6:
        print('FAIL', msg, 'n', g.n, 'R', R, flush=True)


def fam():
    k = rng.randrange(11)
    m = rng.randrange(3, 16)
    H = nx.Graph()
    if k == 0:      # wheel, hub often on R
        H.add_edges_from((0, i) for i in range(1, m + 3))
        H.add_edges_from((i, i + 1) for i in range(1, m + 2))
        H.add_edge(1, m + 2)
    elif k == 1:    # K2,m with chord
        for i in range(2, m + 3):
            H.add_edge(0, i)
            H.add_edge(1, i)
        if rng.random() < .5:
            H.add_edge(0, 1)
    elif k == 2:    # caterpillar with pendants at path vertices: bridges on R
        L = m
        H.add_edges_from((i, i + 1) for i in range(L))
        x = L + 1
        for i in range(L + 1):
            for _ in range(rng.randrange(0, 4)):
                H.add_edge(i, x)
                x += 1
    elif k == 3:    # random tree
        H.add_edges_from((rng.randrange(0, v), v) for v in range(1, 3 * m))
    elif k == 4:    # cycle with pendants
        H.add_edges_from((i, (i + 1) % (m + 3)) for i in range(m + 3))
        x = m + 3
        for i in range(m + 3):
            for _ in range(rng.randrange(0, 3)):
                H.add_edge(i, x)
                x += 1
    elif k == 5:    # stacked triangulation with dropped edges
        faces = [(0, 1, 2), (0, 1, 2)]
        H.add_edges_from([(0, 1), (0, 2), (1, 2)])
        for v in range(3, 3 * m):
            i = rng.randrange(len(faces))
            a, b, c = faces[i]
            faces[i] = (a, b, v)
            faces += [(b, c, v), (a, c, v)]
            H.add_edges_from([(a, v), (b, v), (c, v)])
        drop = rng.choice([0, .2, .4])
        for e in list(H.edges()):
            if rng.random() < drop:
                H.remove_edge(*e)
    elif k == 6:    # grid with dropped edges
        a, b = rng.randrange(2, 8), rng.randrange(2, 8)
        H = nx.convert_node_labels_to_integers(nx.grid_2d_graph(a, b))
        for e in list(H.edges()):
            if rng.random() < rng.choice([0, .15, .3]):
                H.remove_edge(*e)
    elif k == 7:    # fan
        H.add_edges_from((0, i) for i in range(1, m + 2))
        H.add_edges_from((i, i + 1) for i in range(1, m + 1))
    elif k == 8:    # theta graphs: faces that touch R often
        H.add_edges_from((i, i + 1) for i in range(m))
        x = m + 1
        for i in range(0, m, 2):
            H.add_edge(i, x)
            H.add_edge(x, min(i + 2, m))
            x += 1
    elif k == 9:    # a path that winds through one big face: comb
        H.add_edges_from((i, i + 1) for i in range(m))
        H.add_edge(0, m + 1)
        H.add_edge(m, m + 1)
        x = m + 2
        for i in range(1, m):
            H.add_edge(i, x)
            H.add_edge(x, m + 1)
            x += 1
    else:           # two blocks joined by a bridge on R
        a = nx.cycle_graph(m + 3)
        b = nx.relabel_nodes(nx.cycle_graph(m + 3), lambda v: v + 100)
        H = nx.compose(a, b)
        H.add_edge(0, 100)
    if H.number_of_nodes() < 3 or H.number_of_edges() == 0:
        return None
    cc = max(nx.connected_components(H), key=len)
    H = H.subgraph(cc).copy()
    if H.number_of_nodes() < 3:
        return None
    return H


def rand_embedding(H):
    ok, em = nx.check_planarity(H)
    assert ok
    rot = {v: list(em.neighbors_cw_order(v))[::-1] for v in H.nodes()}
    g = nlem.G0(rot)
    assert g.genus0()
    return g


t0 = time.time()
while time.time() - t0 < secs:
    H = fam()
    if H is None:
        continue
    g = rand_embedding(H)
    # pick s,t: hub on R often, or far apart
    d = dict(nx.all_pairs_shortest_path_length(H))
    vs = list(H.nodes())
    s = rng.choice(vs)
    t = max(vs, key=lambda x: (d[s][x], rng.random())) if rng.random() < .6 else rng.choice(vs)
    if s == t:
        continue
    R = nlem.shortest_paths(H, s, t, 4)
    R = rng.choice(R)
    res = nlem.check_structure(g, R, st, rng.choice(['larger', 'smaller', 'random']), rng, fail)
    if res is None:
        continue
    N, q, D, dN = res
    c = nlem.caps(g, rng)
    P = [x for x in q if x[0] == 'c']
    nlem.lam_exact(c, g, N, len(N.nodes), P, None, st, fail, 'm')
    if mode == 'pipe':
        nm = rng.choice(['lo', 'hi', 'two', 'rand', 'blo', 'bhi', 'btwo', 'brand'])
        nlem.pipeline(g, N, q, c, s, t, st, fail, nm, rng)
        st['runs|' + nm] += 1
        st['maxR'] = max(st['maxR'], len(R))
        st['maxS'] = max(st['maxS'], len(q))
        st['maxV_N'] = max(st['maxV_N'], len(N.nodes))
print(json.dumps(st, sort_keys=True))
print('secs', round(time.time() - t0), 'fails', len(fails))
