"""The deterministic part of Proposition 4, against an chooser that picks the clusters and their order.

Lemma 2's first bullet is all the proof of A and B uses, apart from the success event. So any ordered partition whose
clusters have weak diameter <= 2^l in G>=0 is a legal input. If the proof is right, then at every step:
  (S1) A(1) holds for t >= 2.
  (S2) B(l-1) for all r' and the event at (l, r) give A(l) at (l, r).
  (S3) A(l) at (l, r) gives B(l) at (l, r).
Counts of how often each hypothesis held are reported, since a vacuous pass means nothing.
Modes: 'exh3': all restricted digraphs on 3 vertices. 'rand': planar digraphs with n up to 12, potential-built weights.
Controls: mode strings of restricted(): t0 (no alternation), t_minus (t - 1 rounds), noprev, nooffset, wrongdir.
Also a control where the chooser ignores the weak diameter: (S2) is then allowed to fail, and should."""
import itertools, os, random, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from core_check import *

ST = Counter()
EX = {}


def is_restricted(n, arcs):
    if any(w < -1 or w > n for _, _, w in arcs):
        return False
    return bf_all(n, [(u, v, w - 1) for u, v, w in arcs]) is not None


def wpos_all(n, arcs):
    a = [(u, v, max(w, 0)) for u, v, w in arcs]
    return [oracle(n, a, [0 if x == s else INF for x in range(n)]) for s in range(n)]


def random_partition(n, D, d, rng, ignore_diam=False, DV=None):
    """A random ordered partition with weak diameter <= d. Greedy with random order; worst-case preference for large clusters or singletons."""
    vs = list(range(n))
    rng.shuffle(vs)
    style = rng.choice(['big', 'big', 'single', 'mid'])
    blocks = []
    for v in vs:
        placed = False
        if style != 'single' or rng.random() < 0.2:
            order = list(range(len(blocks)))
            rng.shuffle(order)
            for b in order:
                if ignore_diam or all(D[v][x] <= d and D[x][v] <= d for x in blocks[b]):
                    if style == 'mid' and rng.random() < 0.5:
                        continue
                    blocks[b].append(v)
                    placed = True
                    break
        if not placed:
            blocks.append([v])
    rng.shuffle(blocks)
    # worst-case order: arcs on shortest paths go from high dist(V, .) to low, so sorting by ascending dist cuts them all
    if DV is not None and rng.random() < 0.6:
        blocks.sort(key=lambda b: sum(DV[x] for x in b) / len(b))
    idx = [0] * n
    for i, b in enumerate(blocks):
        for v in b:
            idx[v] = i
    return idx


def min_cuts_on_tight(n, inner, dist, idx_prev):
    """min over shortest paths from S to v of the arcs cut by idx_prev. Tight arcs of a restricted graph are acyclic."""
    tight = [(u, v) for u, v, w in inner if dist[u] + w == dist[v]]
    x = [0 if dist[v] == 0 else INF for v in range(n)]
    for _ in range(n + 1):
        ch = False
        for u, v in tight:
            c = 1 if idx_prev[u] > idx_prev[v] else 0
            if x[u] + c < x[v]:
                x[v] = x[u] + c
                ch = True
        if not ch:
            break
    return x


def run_one(n, arcs, R, t, rng, mode='', ignore_diam=False):
    D = wpos_all(n, arcs)
    DV = bf_all(n, arcs)

    def decomp(l, r):
        return random_partition(n, D, 2 ** l, rng, ignore_diam, DV)

    state = {'prev_ok_B': True, 'prev_idx': [], 'cur_idx': [], 'cur_ok_B': True, 'level': 0}

    def hook(l, r, L, idx, best, pot, Phi):
        if l != state['level']:
            if state['level']:
                state['prev_idx'] = state['cur_idx']
                state['prev_ok_B'] = state['cur_ok_B']
            state['level'] = l
            state['cur_idx'] = []
            state['cur_ok_B'] = True
        inner = [a for a in arcs if idx[a[0]] == idx[a[1]]]
        dist = bf_all(n, inner)
        assert dist is not None
        A_ok = best == dist
        ST['n.steps'] += 1
        if l == 1:
            if t >= 2:
                ST['S1.hyp'] += 1
                if not A_ok:
                    ST['S1.FAIL'] += 1
                    EX.setdefault('S1', (n, arcs, idx, best, dist))
        else:
            # event at (l, r)
            mn = [INF] * n
            for ip in state['prev_idx']:
                x = min_cuts_on_tight(n, inner, dist, ip)
                mn = [min(a, b) for a, b in zip(mn, x)]
            ev = max(mn) <= t
            ST['event.true' if ev else 'event.false'] += 1
            if ev and state['prev_ok_B']:
                ST['S2.hyp'] += 1
                if not A_ok:
                    ST['S2.FAIL'] += 1
                    EX.setdefault('S2', (n, arcs, l, r, idx, best, dist))
            elif not A_ok:
                ST['S2.inexact_without_hyp'] += 1
        # B
        low = [a for a in arcs if not (idx[a[0]] > idx[a[1]])]
        B_ok = all(w + pot[u] - pot[v] >= 0 for u, v, w in low)
        if A_ok:
            ST['S3.hyp'] += 1
            if not B_ok:
                ST['S3.FAIL'] += 1
                EX.setdefault('S3', (n, arcs, l, r, idx, best, pot))
        state['cur_ok_B'] = state['cur_ok_B'] and B_ok
        state['cur_idx'].append(idx)

    phi = restricted(n, arcs, rng, R, t, decomp=decomp, hook=hook, mode=mode)
    if arcs and any(w + phi[u] - phi[v] < 0 for u, v, w in arcs):
        ST['final.wrong'] += 1
    else:
        ST['final.right'] += 1


def exh3(R, t, repeats, mode, seed):
    n = 3
    rng = random.Random(seed)
    allarcs = list(itertools.permutations(range(n), 2))
    for ws in itertools.product([None, -1, 0, 1, 2, 3], repeat=len(allarcs)):
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        if not arcs or not is_restricted(n, arcs):
            continue
        ST['instances'] += 1
        for _ in range(repeats):
            run_one(n, arcs, R, t, rng, mode)


def planar_random(rng, nmax):
    """Connected planar graph: a random spanning subgraph of a triangulated grid, verified planar."""
    while True:
        a = rng.randrange(2, 5)
        b = rng.randrange(2, 5)
        if a * b > nmax:
            continue
        n = a * b
        E = []
        for i in range(a):
            for j in range(b):
                x = i * b + j
                if j + 1 < b:
                    E.append((x, x + 1))
                if i + 1 < a:
                    E.append((x, x + b))
                if j + 1 < b and i + 1 < a and rng.random() < 0.5:
                    E.append((x, x + b + 1))
        keep = rng.choice([1, 0.8, 0.6])
        E = [e for e in E if rng.random() < keep]
        g = nx.Graph(E)
        g.add_nodes_from(range(n))
        if not nx.is_connected(g):
            continue
        assert nx.check_planarity(g)[0]
        return n, E


def restricted_weights(n, E, rng):
    """w = 1 + c + p(u) - p(v) >= -1, with long chains of -1 arcs. Mean of every cycle at least 1."""
    style = rng.choice(['chain', 'chain', 'chain', 'rand', 'steep'])
    p = [0] * n
    if style == 'rand':
        p = [rng.randrange(0, 2 * n) for _ in range(n)]
    else:
        # DFS order, rising by 2 along it
        adj = {v: [] for v in range(n)}
        for a, b in E:
            adj[a].append(b)
            adj[b].append(a)
        order = []
        seen = set()
        st = [rng.randrange(n)]
        while st:
            x = st.pop()
            if x in seen:
                continue
            seen.add(x)
            order.append(x)
            nb = adj[x][:]
            rng.shuffle(nb)
            st += nb
        cur = 0
        for v in order:
            p[v] = cur
            if style == 'steep' or rng.random() < 0.7:
                cur += 2
            else:
                cur -= rng.randrange(1, 6)
    arcs = []
    for a, b in E:
        for u, v in ((a, b), (b, a)):
            diff = p[u] - p[v]
            c = max(0, -2 - diff) + rng.choice([0, 0, 0, 1, 2])
            w = 1 + c + diff
            if w <= n:
                arcs.append((u, v, w))
    return arcs


def rand_lane(R, t, secs, nmax, mode, seed, ignore_diam=False):
    rng = random.Random(seed)
    end = time.time() + secs
    while time.time() < end:
        n, E = planar_random(rng, nmax)
        arcs = restricted_weights(n, E, rng)
        if not arcs or not is_restricted(n, arcs):
            ST['skip'] += 1
            continue
        ST['instances'] += 1
        ST['max_n'] = max(ST['max_n'], n)
        run_one(n, arcs, R, t, rng, mode, ignore_diam)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'exh3':
        exh3(int(a[1]), int(a[2]), int(a[3]), a[4] if len(a) > 4 and a[4] != '-' else '', 11)
    else:
        rand_lane(int(a[1]), int(a[2]), float(a[3]), int(a[4]), a[5] if len(a) > 5 and a[5] != '-' else '', 12, len(a) > 6)
    print(' '.join(a), {k: ST[k] for k in sorted(ST)})
    if EX:
        print('EX', {k: EX[k] for k in EX})
