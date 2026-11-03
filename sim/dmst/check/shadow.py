"""Is the virtual network G' of Fischer-Oshman (DISC 2019, Section 5) planar, and what is its hop diameter?

Literal G' of the conference text:
  (a) all edges internal to some subgraph G_i;
  (b) the shadow copies (u', v') of all edges of G;
  (c) for each marked node v_i, the pair (v_i', v_i) and (v_i, v_i').
Variant `all`: (c) for every vertex that lies in some G_i, which is what a bound diam(G') <= 2 diam(G) + 1 would need.

Vertices outside all G_i are in G' as isolated real vertices in the literal reading; we leave them out of the diameter,
since they do nothing, and report it both ways where it matters.
"""
import random
import sys
import networkx as nx


def voronoi(G, centres):
    """Vertex-disjoint connected subgraphs G_i: BFS regions around the centres."""
    owner = {}
    frontier = list(centres)
    for c in centres:
        owner[c] = c
    while frontier:
        nxt = []
        for x in frontier:
            for y in G[x]:
                if y not in owner:
                    owner[y] = owner[x]
                    nxt.append(y)
        frontier = nxt
    return owner


def build(G, owner, marked, all_links):
    H = nx.Graph()
    for u, v in G.edges:
        H.add_edge(('s', u), ('s', v))           # (b)
        if owner.get(u) is not None and owner.get(u) == owner.get(v):
            H.add_edge(('r', u), ('r', v))       # (a)
    links = [v for v in G.nodes if v in owner] if all_links else marked
    for v in links:
        H.add_edge(('s', v), ('r', v))           # (c)
    return H


def report(name, G, centres):
    owner = voronoi(G, centres)
    assert nx.check_planarity(G)[0]
    lit = build(G, owner, centres, False)
    full = build(G, owner, centres, True)
    row = dict(name=name, n=G.number_of_nodes(), D=nx.diameter(G),
               lit_planar=nx.check_planarity(lit)[0], lit_conn=nx.is_connected(lit),
               lit_diam=nx.diameter(lit) if nx.is_connected(lit) else None,
               bound=2 * nx.diameter(G) + 1,
               all_planar=nx.check_planarity(full)[0],
               all_diam=nx.diameter(full) if nx.is_connected(full) else None)
    print(row, flush=True)
    return row


def main():
    # A wheel: D = 2, one G_1 = the rim (the hub is left out), so the real copy of the rim hangs on one link.
    for k in (10, 50, 200):
        G = nx.wheel_graph(k + 1)
        owner_centre = [1]
        owner = {v: 1 for v in range(1, k + 1)}
        lit = build(G, owner, owner_centre, False)
        full = build(G, owner, owner_centre, True)
        print(dict(name=f'wheel rim {k}', D=nx.diameter(G), bound=2 * nx.diameter(G) + 1,
                   lit_planar=nx.check_planarity(lit)[0], lit_diam=nx.diameter(lit),
                   all_planar=nx.check_planarity(full)[0], all_diam=nx.diameter(full)), flush=True)
    # Grids with one or several regions.
    for a, b, c in ((3, 3, 1), (4, 4, 1), (5, 5, 2), (8, 8, 3), (12, 12, 5)):
        G = nx.convert_node_labels_to_integers(nx.grid_2d_graph(a, b))
        rng = random.Random(a * 100 + b + c)
        report(f'grid {a}x{b} regions {c}', G, rng.sample(sorted(G.nodes), c))
    # Random planar graphs: literal G' must be planar always, as a 1-sum of blocks.
    rng = random.Random(77)
    bad, tot, allnp = 0, 0, 0
    for _ in range(400):
        n = rng.randrange(6, 60)
        faces, E = [(0, 1, 2), (0, 1, 2)], {(0, 1), (0, 2), (1, 2)}
        for v in range(3, n):
            i = rng.randrange(len(faces))
            x, y, z = faces[i]
            faces[i] = (x, y, v)
            faces += [(y, z, v), (x, z, v)]
            E |= {(x, v), (y, v), (z, v)}
        G = nx.Graph(sorted(E))
        cs = rng.sample(sorted(G.nodes), rng.randrange(1, 6))
        owner = voronoi(G, cs)
        lit = build(G, owner, cs, False)
        full = build(G, owner, cs, True)
        tot += 1
        bad += not nx.check_planarity(lit)[0]
        allnp += not nx.check_planarity(full)[0]
    print(dict(random_stacked=tot, literal_nonplanar=bad, all_links_nonplanar=allnp), flush=True)


if __name__ == '__main__':
    main()
