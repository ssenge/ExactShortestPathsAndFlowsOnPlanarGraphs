"""Generators: all planar embeddings of a small graph (incremental edge insertion into faces),
spanning trees, parent arrays, structured families and random planar maps."""
import sys, itertools, random, collections
sys.dont_write_bytecode = True
from mine import mkidx, corner_faces


def cyc_orders(lst):
    if len(lst) <= 1:
        yield list(lst); return
    f = lst[0]
    for p in itertools.permutations(lst[1:]):
        yield [f] + list(p)


def embeddings(V, E):
    """all rotation systems of the connected simple graph (V, E) that are planar; each once."""
    adj = collections.defaultdict(list)
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    # BFS spanning tree T0
    r0 = V[0]; seen = {r0}; T0 = []; q = [r0]
    while q:
        v = q.pop(0)
        for u in adj[v]:
            if u not in seen:
                seen.add(u); T0.append((v, u)); q.append(u)
    t0 = set(frozenset(e) for e in T0)
    rest = [e for e in E if frozenset(e) not in t0]
    tadj = collections.defaultdict(list)
    for a, b in T0:
        tadj[a].append(b); tadj[b].append(a)
    per = [list(cyc_orders(tadj[v])) for v in V]
    def rec(rot, i):
        if i == len(rest):
            yield {v: list(rot[v]) for v in V}; return
        u, v = rest[i]
        idx = mkidx(rot)
        fid, _ = corner_faces(rot, idx)
        for ju in range(len(rot[u])):
            for jv in range(len(rot[v])):
                if fid[(u, ju)] != fid[(v, jv)]:
                    continue
                r2 = dict(rot)
                r2[u] = rot[u][:ju] + [v] + rot[u][ju:]
                r2[v] = rot[v][:jv] + [u] + rot[v][jv:]
                yield from rec(r2, i + 1)
    for combo in itertools.product(*per):
        rot = {v: combo[t] for t, v in enumerate(V)}
        yield from rec(rot, 0)


def spanning_trees(V, E):
    n = len(V)
    for S in itertools.combinations(E, n - 1):
        p = {v: v for v in V}
        def find(a):
            while p[a] != a:
                p[a] = p[p[a]]; a = p[a]
            return a
        ok = True
        for a, b in S:
            x, y = find(a), find(b)
            if x == y:
                ok = False; break
            p[x] = y
        if ok:
            yield S


def parents(V, S, r):
    adj = collections.defaultdict(list)
    for a, b in S:
        adj[a].append(b); adj[b].append(a)
    par = {r: None}; q = [r]
    while q:
        v = q.pop()
        for u in adj[v]:
            if u not in par:
                par[u] = v; q.append(u)
    return par


# ---------- random planar maps: random tree with random rotations, then edges inserted into faces


def random_map(n, extra, rng, multi_corner_bias=0.0):
    """random tree on n vertices (random Pruefer-like attachment), random rotations, then `extra`
    random non-parallel edges each between two corners of one face. Not geometric."""
    V = list(range(n))
    rot = {v: [] for v in V}
    order = V[:]; rng.shuffle(order)
    for t in range(1, n):
        v = order[t]
        # attach to a random earlier vertex; with bias, prefer few hubs
        if multi_corner_bias and rng.random() < multi_corner_bias:
            u = order[rng.randrange(min(t, 3))]
        else:
            u = order[rng.randrange(t)]
        rot[u].insert(rng.randrange(len(rot[u]) + 1), v)
        rot[v].insert(rng.randrange(len(rot[v]) + 1), u)
    E = set(frozenset((a, b)) for a in V for b in rot[a])
    tries = 0
    added = 0
    while added < extra and tries < extra * 20:
        tries += 1
        idx = mkidx(rot)
        fid, faces = corner_faces(rot, idx)
        f = rng.choice(faces)
        if len(f) < 4:
            continue
        a = rng.choice(f); b = rng.choice(f)
        u, v = a[0], b[0]
        if u == v or frozenset((u, v)) in E:
            continue
        rot[u] = rot[u][:a[1]] + [v] + rot[u][a[1]:]
        rot[v] = rot[v][:b[1]] + [u] + rot[v][b[1]:]
        E.add(frozenset((u, v))); added += 1
    return V, rot


def edges_of(rot):
    return sorted({tuple(sorted((a, b))) for a in rot for b in rot[a]})


def random_spanning_tree(V, rot, rng, mode):
    E = edges_of(rot)
    adj = {v: list(rot[v]) for v in V}
    r = rng.choice(V)
    if mode == 'bfs':
        par = {r: None}; q = collections.deque([r])
        while q:
            v = q.popleft()
            nb = adj[v][:]; rng.shuffle(nb)
            for u in nb:
                if u not in par:
                    par[u] = v; q.append(u)
    elif mode == 'dfs':
        par = {r: None}
        st = [(r, iter(sorted(adj[r], key=lambda _: rng.random())))]
        while st:
            v, itr = st[-1]
            for u in itr:
                if u not in par:
                    par[u] = v; st.append((u, iter(sorted(adj[u], key=lambda _: rng.random())))); break
            else:
                st.pop()
    else:  # random (Kruskal on random weights), rooted at r
        ee = E[:]; rng.shuffle(ee)
        p = {v: v for v in V}
        def find(a):
            while p[a] != a:
                p[a] = p[p[a]]; a = p[a]
            return a
        S = []
        for a, b in ee:
            x, y = find(a), find(b)
            if x != y:
                p[x] = y; S.append((a, b))
        par = parents(V, S, r)
    return r, par
