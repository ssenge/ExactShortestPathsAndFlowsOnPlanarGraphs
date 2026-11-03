# Large worst-case families, built here and not taken from dmst.py. Each network passes
# nx.check_planarity and nx.is_connected before it is written. Format for `dm file`:
#   label n m r cor  edges...  k  arcs(u v w)...
import sys, random
import networkx as nx

rng = random.Random(int(sys.argv[2]))
out = open(sys.argv[1], 'w')
count = 0

def emit(label, n, E, arcs, r, cor=0):
    global count
    G = nx.Graph()
    G.add_nodes_from(range(n))
    E = sorted({tuple(sorted(e)) for e in E} | {tuple(sorted((u, v))) for u, v, _ in arcs})
    G.add_edges_from(E)
    assert nx.is_connected(G), label
    ok, _ = nx.check_planarity(G)
    assert ok, label
    out.write(f'{label} {n} {len(E)} {r} {cor}\n')
    out.write(' '.join(f'{u} {v}' for u, v in E) + '\n')
    out.write(f'{len(arcs)}\n')
    out.write(' '.join(f'{u} {v} {w}' for u, v, w in arcs) + '\n')
    count += 1

def ruler(i):
    return (i & -i).bit_length() - 1

def ruler_path(k, top=None, jitter=False):
    # vertex 0 is r, 1..2^k a path; the edge i,i+1 has level ruler(i). Level l costs 4^l. r enters dearly.
    N = 2 ** k
    arcs = []
    for i in range(1, N):
        c = 4 ** ruler(i)
        arcs.append((i, i + 1, c + (rng.randint(0, 1) if jitter else 0)))
        arcs.append((i + 1, i, c + (rng.randint(0, 1) if jitter else 0)))
    arcs.append((0, 1, 4 ** (k + 1)))
    return N + 1, arcs

def per_head_shift(arcs, lo=-50, hi=50):
    # Step 1 must undo these. Optimal trees do not change, weights go negative.
    s = {}
    res = []
    for u, v, w in arcs:
        s.setdefault(v, rng.randint(lo, hi))
        res.append((u, v, w + s[v]))
    return res

for k in range(1, 12):
    n, a = ruler_path(k)
    emit(f'ruler_k{k}', n, [], a, 0)
    n, a = ruler_path(k, jitter=True)
    emit(f'rulerj_k{k}', n, [], a, 0)
    emit(f'rulerneg_k{k}', n, [], per_head_shift(a), 0)
    # the same on the square of the path, whose chords carry no arc: they are bare network edges
    # inside super-vertices, so tight paths use them
    chords = [(i, i + 2) for i in range(1, n - 2)]
    emit(f'rulerP2_k{k}', n, chords, a, 0)
    # the branching lane: without the root
    b = [(u - 1, v - 1, 4 ** (k + 1) - w) for u, v, w in a if u != 0]
    if n - 1 >= 2:
        emit(f'rulercor_k{k}', n - 1, [], b, 0, 1)

# Pendants. On each path vertex a pendant p with v->p of weight 0, and p->v dear (large finite d) or absent (d infinite).
for k in range(1, 11):
    n, a = ruler_path(k)
    N = n - 1
    for mode in ['dear', 'inf', 'mix']:
        arcs = list(a)
        m = n
        for i in range(1, N + 1):
            arcs.append((i, m, 0))
            if mode == 'dear' or (mode == 'mix' and rng.random() < .5):
                arcs.append((m, i, 4 ** (k + 3)))
            m += 1
        emit(f'pend_{mode}_k{k}', m, [], arcs, 0)

# Rings of rings, by threes. Forward arcs cheap, reverse arcs very dear (10^6 scale), so network edges inside
# super-vertices carry arcs of large weight.
def rings(k, heavy):
    N = 3 ** k
    arcs = []
    for lev in range(k):
        step = 3 ** lev
        for i in range(0, N, 3 * step):
            blk = [i + j * step for j in range(3)]
            for j in range(3):
                a, b = blk[j], blk[(j + 1) % 3]
                # planarity: use the first vertices of blocks, a tree of triangles
                arcs.append((a + 1, b + 1, 4 ** lev))
                arcs.append((b + 1, a + 1, heavy))
    arcs.append((0, 1, 4 ** (k + 2)))
    return N + 1, arcs
for k in range(1, 7):
    n, a = rings(k, 10 ** 6)
    # distinct arcs only; keep the first of parallels at the top of the tree
    seen = {}
    for u, v, w in a:
        if u != v:
            seen[(u, v)] = min(w, seen.get((u, v), w))
    arcs = [(u, v, w) for (u, v), w in seen.items()]
    G = nx.Graph([(u, v) for u, v, _ in arcs])
    if nx.check_planarity(G)[0] and nx.is_connected(G) and G.number_of_nodes() == n:
        emit(f'rings_k{k}', n, [], arcs, 0)
        emit(f'ringsneg_k{k}', n, [], per_head_shift(arcs), 0)

# One long cycle, with an entry far from any c, dear back arcs, and many ties.
for m in [3, 5, 8, 16, 33, 64, 200, 1000]:
    arcs = [(i, i % m + 1, 0) for i in range(1, m + 1)]
    arcs += [(i % m + 1, i, rng.randint(0, 3)) for i in range(1, m + 1)]
    arcs.append((0, 1, 7))
    emit(f'cycle0_m{m}', m + 1, [], arcs, 0)
    # the same, all entries at r through a wheel: every vertex has a dear arc from r, on a planar wheel
    arcs2 = [(i, i % m + 1, 0) for i in range(1, m + 1)]
    arcs2 += [(0, i, rng.randint(1, 5)) for i in range(1, m + 1)]
    if m >= 3:
        emit(f'wheel_m{m}', m + 1, [], arcs2, 0)
        emit(f'wheelcor_m{m}', m, [(i - 1, i % m) for i in range(1, m + 1)], [(i - 1, i % m, 5) for i in range(1, m + 1)], 0, 1)

# Snake on a grid: arcs only along a Hamiltonian snake with ruler weights, and all other grid edges bare.
# Bare edges join far parts of the snake, and they become usable once both ends are in one super-vertex.
for s in [3, 4, 6, 8, 12, 16, 24, 32, 45]:
    idx = lambda x, y: x * s + (y if x % 2 == 0 else s - 1 - y)
    E = []
    for x in range(s):
        for y in range(s):
            if x + 1 < s:
                E.append((idx(x, y), idx(x + 1, y)))
            if y + 1 < s:
                E.append((idx(x, y), idx(x, y + 1)))
    N = s * s
    # vertex N-1 is r with a dear entry at the far end
    arcs = []
    for i in range(0, N - 2):
        c = 4 ** ruler(i + 1)
        arcs.append((i, i + 1, c))
        arcs.append((i + 1, i, c))
    big = 4 ** 14
    arcs.append((N - 1, N - 2, big))
    emit(f'snake_s{s}', N, E, arcs, N - 1)
    emit(f'snakeneg_s{s}', N, E, per_head_shift(arcs), N - 1)

# Unreached parts that aim into the reached set with very cheap arcs, around a small reached set.
for m in [4, 16, 64, 256]:
    arcs = [(0, 1, 5), (1, 2, 1), (2, 1, 1)]
    E = [(i, i + 1) for i in range(m)]
    for i in range(3, m):
        arcs.append((i, i - 1 if i > 3 else 2, -10 ** 6))
        arcs.append((i - 1 if i > 3 else 2, i, 10 ** 6)) if False else None
    arcs.append((1, 0, -10 ** 6))
    emit(f'smallreach_m{m}', m + 1, E, arcs, 0)

print('families written', count)
