"""Numerical attack on Lemma V (virtual-source convergecast over a separator hierarchy).

Hierarchy: recursive BFS-layer separators; child = component of G[X]-S plus the S-vertices adjacent to it.
This satisfies: non-separator vertices lie in exactly one child; every path in G[X] between
different children meets S (7b).  Hub distances d~_X are exact G[X]-distances times a random factor
in [1, 1+eps] (never underestimates).
Also tests the lty Thm 4 query (single min-depth separating bag) to see whether it can fail.
"""
import random, sys, heapq
import networkx as nx

INF = float('inf')


def dijkstra(adj, nodes, src):
    dist = {src: 0}
    pq = [(0, src)]
    while pq:
        d, x = heapq.heappop(pq)
        if d > dist.get(x, INF):
            continue
        for y, w in adj.get(x, ()):  # adj: x -> list of (y,w)
            if y in nodes and d + w < dist.get(y, INF):
                dist[y] = d + w
                heapq.heappush(pq, (d + w, y))
    return dist


def build_hier(U, X, rng, leaf, depth=0, anc_hubs=frozenset(), out=None):
    """U undirected nx graph. returns list of bag dicts."""
    bag = {'X': frozenset(X), 'depth': depth, 'hubs_anc': frozenset(anc_hubs & set(X)), 'children': []}
    out.append(bag)
    if len(X) <= leaf:
        bag['leaf'] = True
        bag['S'] = frozenset()
        return bag
    bag['leaf'] = False
    H = U.subgraph(X)
    for attempt in range(20):
        r = rng.choice(list(X))
        lay = nx.single_source_shortest_path_length(H, r)
        maxd = max(lay.values())
        if maxd < 2:
            continue
        L = rng.randint(1, maxd - 1)
        S = {v for v, d in lay.items() if d == L}
        rest = H.subgraph(set(X) - S)
        comps = list(nx.connected_components(rest))
        if len(comps) >= 2 and max(len(c) for c in comps) < len(X):
            break
    else:
        bag['leaf'] = True
        bag['S'] = frozenset()
        return bag
    bag['S'] = frozenset(S)
    newhubs = set(anc_hubs) | S
    for c in comps:
        child = set(c) | {s for s in S if any(nb in c for nb in U.neighbors(s))}
        if not nx.is_connected(U.subgraph(child)):
            continue
        ch = build_hier(U, child, rng, leaf, depth + 1, frozenset(newhubs), out)
        bag['children'].append(ch)
    return bag


def run(trial_seed, eps=0.25):
    rng = random.Random(trial_seed)
    rows, cols = rng.randint(3, 7), rng.randint(3, 7)
    U = nx.grid_2d_graph(rows, cols)
    for r in range(rows - 1):
        for c in range(cols - 1):
            if rng.random() < 0.5:
                U.add_edge((r, c), (r + 1, c + 1))
    U = nx.convert_node_labels_to_integers(U)
    # random directed weights; some arcs missing; zeros allowed
    adj = {}
    for u, v in U.edges():
        for a, b in [(u, v), (v, u)]:
            if rng.random() < 0.8:
                adj.setdefault(a, []).append((b, rng.choice([0, 1, 2, 5, 20, 100])))
    V = set(U.nodes())
    bags = []
    build_hier(U, V, rng, leaf=rng.randint(2, 6), out=bags)
    phi = {v: rng.choice([0, 3, 50, 10**6]) for v in V}
    # true distances from virtual source
    true = {v: INF for v in V}
    for u in V:
        du = dijkstra(adj, V, u)
        for v, d in du.items():
            true[v] = min(true[v], phi[u] + d)
    # per bag: hubs, dX
    est = {v: INF for v in V}
    fac = {}
    def f(key):
        if key not in fac:
            fac[key] = 1 + eps * rng.choice([0, 0, 1, rng.random()])
        return fac[key]
    radj = {}
    for a, lst in adj.items():
        for b, w in lst:
            radj.setdefault(b, []).append((a, w))
    for bag in bags:
        X = bag['X']
        if bag['leaf']:
            for u in X:
                du = dijkstra(adj, X, u)
                for v, d in du.items():
                    est[v] = min(est[v], phi[u] + d)
            continue
        hubs = bag['hubs_anc'] | bag['S']
        for h in hubs:
            to_h = dijkstra(radj, X, h)   # dist_{G[X]}(u,h)
            from_h = dijkstra(adj, X, h)  # dist_{G[X]}(h,v)
            A = min((phi[u] + to_h[u] * f(('to', id(bag), u, h)) for u in X if u in to_h), default=INF)
            for v, d in from_h.items():
                est[v] = min(est[v], A + d * f(('from', id(bag), h, v)))
    bad = 0
    for v in V:
        if not (true[v] <= est[v] + 1e-9 and est[v] <= (1 + eps) * true[v] + 1e-9):
            bad += 1
            print('LEMMA V FAIL', trial_seed, v, true[v], est[v])
    return bad, bags, adj, U


def lty_query_test(seed):
    """Real source s; lty's query uses only the min-depth bag separating s and u, with G[X]-local labels."""
    bad, bags, adj, U = run(seed, eps=0.0)
    rng = random.Random(seed + 999)
    V = set(U.nodes())
    s = rng.choice(list(V))
    true = dijkstra(adj, V, s)
    radj = {}
    for a, lst in adj.items():
        for b, w in lst:
            radj.setdefault(b, []).append((a, w))
    root = bags[0]
    fails = 0
    for u in V:
        if u == s:
            continue
        # walk down from root to find the min-depth bag X where s,u are separated
        X = root
        while True:
            if X['leaf']:
                break
            if s in X['S'] or u in X['S']:
                break
            nxt = [c for c in X['children'] if s in c['X'] and u in c['X']]
            if not nxt:
                break
            X = nxt[0]
        Xs = X['X']
        if X['leaf']:
            q = dijkstra(adj, Xs, s).get(u, INF)
        else:
            hubs = X['hubs_anc'] | X['S']
            ds = dijkstra(adj, Xs, s)
            q = INF
            for h in hubs:
                dh = dijkstra(adj, Xs, h)
                q = min(q, ds.get(h, INF) + dh.get(u, INF))
        if q != true.get(u, INF):
            fails += 1
    return fails


if __name__ == '__main__':
    tot = 0
    for sd in range(int(sys.argv[1]) if len(sys.argv) > 1 else 200):
        b, *_ = run(sd)
        tot += b
    print('Lemma V failures:', tot)
    lf = 0
    for sd in range(100):
        lf += lty_query_test(sd) > 0
    print('lty single-bag query: instances with a wrong distance:', lf, 'of 100')
