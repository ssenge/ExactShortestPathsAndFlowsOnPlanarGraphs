# Pool of connected planar networks. Every graph written here has passed nx.check_planarity
# and nx.is_connected. The C++ tester only places arcs on the edges of these graphs, so all
# its instances are planar (H is a subgraph of the bidirected G).
# Usage: gen_pool.py out.txt seed
import sys, random
import networkx as nx
from networkx.generators.atlas import graph_atlas_g

def triangulation(n, rng, flips):
    # Random insertion into faces, then random edge flips. Faces are kept as vertex triples.
    faces = [(0, 1, 2), (0, 2, 1)]
    edges = {frozenset(e) for e in [(0, 1), (1, 2), (0, 2)]}
    for v in range(3, n):
        i = rng.randrange(len(faces))
        a, b, c = faces[i]
        faces[i] = (a, b, v)
        faces.append((b, c, v))
        faces.append((c, a, v))
        edges |= {frozenset((v, a)), frozenset((v, b)), frozenset((v, c))}
    for _ in range(flips):
        i = rng.randrange(len(faces))
        a, b, c = faces[i]
        # the face across edge (a,b)
        j = None
        for k, f in enumerate(faces):
            if k != i and {a, b} <= set(f):
                j = k
                break
        if j is None:
            continue
        d = [x for x in faces[j] if x not in (a, b)][0]
        if d == c or frozenset((c, d)) in edges:
            continue
        edges.discard(frozenset((a, b)))
        edges.add(frozenset((c, d)))
        faces[i] = (a, d, c)
        faces[j] = (d, b, c)
    return edges

def add(pool, seen, G, label):
    G = nx.convert_node_labels_to_integers(G)
    G = nx.Graph(G)
    G.remove_edges_from(list(nx.selfloop_edges(G)))
    if G.number_of_nodes() == 0 or not nx.is_connected(G):
        return
    ok, _ = nx.check_planarity(G)
    if not ok:
        return
    key = (G.number_of_nodes(), tuple(sorted(tuple(sorted(e)) for e in G.edges())))
    if key in seen:
        return
    seen.add(key)
    pool.append((label, G))

def main():
    out, seed = sys.argv[1], int(sys.argv[2])
    rng = random.Random(seed)
    pool, seen = [], set()
    for G in graph_atlas_g():
        if G.number_of_nodes() >= 1:
            add(pool, seen, G, 'atlas')
    natlas = len(pool)
    for n in [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24, 28, 32, 33, 40, 48, 56, 64, 65, 80, 100, 129]:
        for rep in range(40 if n <= 33 else 10):
            flips = rng.choice([0, n, 5 * n])
            E = triangulation(n, rng, flips)
            G = nx.Graph()
            G.add_nodes_from(range(n))
            G.add_edges_from(tuple(e) for e in E)
            add(pool, seen, G, 'tri')
            # sparser subgraphs that stay connected
            for keep in [0.8, 0.6, 0.45]:
                H = G.copy()
                es = list(H.edges())
                rng.shuffle(es)
                for e in es[:int(len(es) * (1 - keep))]:
                    H.remove_edge(*e)
                    if not nx.is_connected(H):
                        H.add_edge(*e)
                add(pool, seen, H, 'subtri')
    for a in range(2, 12):
        for b in range(a, 12):
            add(pool, seen, nx.grid_2d_graph(a, b), 'grid')
            add(pool, seen, nx.triangular_lattice_graph(a, b), 'trilat')
            if a >= 3:
                add(pool, seen, nx.grid_2d_graph(a, b, periodic=(True, False)), 'cylinder')
    for n in range(4, 70, 3):
        add(pool, seen, nx.wheel_graph(n), 'wheel')
        add(pool, seen, nx.cycle_graph(n), 'cycle')
        add(pool, seen, nx.path_graph(n), 'path')
        add(pool, seen, nx.star_graph(n), 'star')
        add(pool, seen, nx.complete_bipartite_graph(2, n), 'k2m')
        add(pool, seen, nx.ladder_graph(n), 'ladder')
        add(pool, seen, nx.circular_ladder_graph(max(n, 3)), 'prism')
        B = nx.cycle_graph(n)
        B.add_edges_from((n, i) for i in range(n))
        B.add_edges_from((n + 1, i) for i in range(n))
        add(pool, seen, B, 'bipyramid')
        F = nx.path_graph(n)
        F.add_edges_from((n, i) for i in range(n))
        add(pool, seen, F, 'fan')
    for n in [10, 20, 40, 80]:
        for rep in range(10):
            add(pool, seen, nx.random_labeled_tree(n, seed=rng.randrange(10**9)), 'tree')
    with open(out, 'w') as f:
        f.write(f'{len(pool)}\n')
        for label, G in pool:
            es = sorted(tuple(sorted(e)) for e in G.edges())
            f.write(f'{label} {G.number_of_nodes()} {len(es)} ' + ' '.join(f'{u} {v}' for u, v in es) + '\n')
    from collections import Counter
    print('graphs', len(pool), 'atlas', natlas, 'max n', max(G.number_of_nodes() for _, G in pool))
    print(Counter(l for l, _ in pool))
    print('by n (atlas):', sorted(Counter(G.number_of_nodes() for l, G in pool if l == 'atlas').items()))

main()
