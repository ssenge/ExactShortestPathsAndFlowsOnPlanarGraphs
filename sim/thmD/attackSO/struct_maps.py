"""Small structured plane graphs (grids with diagonals, ladders, wheels, rings with a hub,
grids with parallel edges and subdivisions) in the enum_maps.py format, key '0'.
Usage: python3 -I struct_maps.py OUT.json"""
import sys
import os
import json
import random
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv
T = adv.T
out = []
rng = random.Random(7)


def add(B):
    if B.connected() and B.euler_ok():
        out.append((B.n, [list(e) for e in B.ends], B.rot))


for a in range(2, 5):
    for b in range(a, 6):
        if a * b > 15:
            continue
        add(T.Builder.from_nx(nx.grid_2d_graph(a, b)))
        for k in range(2):
            G = nx.grid_2d_graph(a, b)
            used = set()
            for _ in range(rng.randint(1, a * b // 3 + 1)):
                r, c = rng.randrange(a - 1), rng.randrange(b - 1)
                if (r, c) in used:
                    continue
                used.add((r, c))
                G.add_edge((r, c), (r + 1, c + 1)) if rng.random() < 0.5 else G.add_edge((r + 1, c), (r, c + 1))
            add(T.Builder.from_nx(G))
        B = T.Builder.from_nx(nx.grid_2d_graph(a, b))
        for _ in range(2):
            B.add_parallel(rng.randrange(len(B.ends)))
        B.subdivide(rng.randrange(len(B.ends)))
        add(B)
for n in range(5, 10):
    add(T.Builder.from_nx(nx.wheel_graph(n)))
for L in range(3, 6):
    for k in (2, 3):
        G = nx.Graph()
        for r in range(k):
            for i in range(L):
                G.add_edge((r, i), (r, (i + 1) % L))
        for r in range(k - 1):
            for i in range(L):
                G.add_edge((r, i), (r + 1, i))
        G.add_node('c')
        for i in range(L):
            G.add_edge('c', (0, i))
        add(T.Builder.from_nx(G))
json.dump({'0': out}, open(sys.argv[1], 'w'))
print(len(out), 'graphs, n up to', max(o[0] for o in out))
