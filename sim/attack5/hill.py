"""Hill climbing on combinatorial plane graphs, spanning trees, roots and start corners, to push
the proof's quantities toward their bounds (and past them, if possible).
usage: python3 -I hill.py OBJ SEED ITERS NMAX
OBJ: chord (max in_j/(W_{j-1}+W') at chord steps), side (max side/n of a step-3 answer),
     inj (max in_j/n, chosen j>1), in1 (in_1/n), outm (out_m/n), wjm1 (W_{j-1}/n)"""
import sys, os, random, copy, collections
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fams import FAMS, add_edge, local_chords
from gen import random_spanning_tree, parents, edges_of
from mine import Fail, mkidx, run, corner_faces, is_planar_rot
import harness as H

OBJ, seed, iters, nmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
KEY = {'chord': 'chord_step_ratio', 'side': 'virt_side_over_n', 'inj': 'virt_in_over_n_j>1', 'in1': 'in1_over_n',
       'outm': 'outm_over_n', 'wjm1': 'Wjm1_over_n'}[OBJ]


def connected_tree(V, S):
    p = {v: v for v in V}
    def f(a):
        while p[a] != a:
            p[a] = p[p[a]]; a = p[a]
        return a
    for a, b in S:
        x, y = f(a), f(b)
        if x == y:
            return False
        p[x] = y
    return len(S) == len(V) - 1


def evaluate(V, rot, S, rk_list):
    best = (-1.0, None)
    for r, k in rk_list:
        if k >= len(rot[r]):
            continue
        par = parents(V, S, r)
        try:
            res = run(V, rot, mkidx(rot), par, r, k, deep=False)
        except Fail as ex:
            print('FAIL', repr(ex), 'rot=', rot, 'S=', S, 'r=', r, 'k=', k, flush=True)
            return (9.0, (r, k))
        v = res['mx'].get(KEY, -1.0)
        if v > best[0]:
            best = (v, (r, k))
    return best


def mutate(V, rot, S):
    V = V[:]; rot = {v: list(rot[v]) for v in rot}; S = list(S)
    Sset = set(frozenset(e) for e in S)
    E = set(frozenset(e) for e in edges_of(rot))
    op = rng.choice(['chord', 'chord', 'lchord', 'rmchord', 'pendant', 'pendant', 'subdiv', 'swap', 'retree'])
    if op in ('chord', 'lchord'):
        fid, faces = corner_faces(rot, mkidx(rot))
        f = rng.choice(faces)
        if len(f) < 4:
            return None
        a = rng.choice(f)
        if op == 'lchord':
            s = f.index(a); b = f[(s + rng.randint(2, min(4, len(f) - 1))) % len(f)]
        else:
            b = rng.choice(f)
        if a[0] == b[0] or frozenset((a[0], b[0])) in E:
            return None
        add_edge(rot, a[0], a[1], b[0], b[1])
    elif op == 'rmchord':
        ch = [e for e in E if e not in Sset]
        if not ch:
            return None
        u, v = tuple(rng.choice(ch)); rot[u].remove(v); rot[v].remove(u)
    elif op == 'pendant':
        if len(V) >= nmax:
            return None
        u = rng.choice(V); w = max(V) + 1; V.append(w)
        rot[u].insert(rng.randrange(len(rot[u]) + 1), w); rot[w] = [u]; S.append((u, w))
    elif op == 'subdiv':
        if len(V) >= nmax:
            return None
        u, v = rng.choice(S); w = max(V) + 1; V.append(w)
        rot[u][rot[u].index(v)] = w; rot[v][rot[v].index(u)] = w; rot[w] = [u, v]
        S = [e for e in S if frozenset(e) != frozenset((u, v))] + [(u, w), (w, v)]
    elif op == 'swap':
        ch = [e for e in E if e not in Sset]
        if not ch:
            return None
        e = tuple(rng.choice(ch))
        # remove a random tree edge on the fundamental cycle of e
        par = parents(V, S, V[0])
        from mine import tpath
        p = tpath(par, e[0], e[1])
        i = rng.randrange(len(p) - 1)
        rm = frozenset((p[i], p[i + 1]))
        S = [x for x in S if frozenset(x) != rm] + [e]
    else:
        _, par = random_spanning_tree(V, rot, rng, rng.choice(['bfs', 'dfs', 'rand']))
        S = [(v, par[v]) for v in V if par[v] is not None]
    if not is_planar_rot(rot, mkidx(rot)) or not connected_tree(V, S):
        return None
    if any(rot[v] == [] for v in V):
        return None
    return V, rot, S


fam = rng.choice(['loc_few', 'loc_many', 'sibling', 'hub', 'tree_rand', 'cactus', 'strip'])
V, rot = FAMS[fam](rng.randint(10, nmax), rng)
_, par = random_spanning_tree(V, rot, rng, 'bfs')
S = [(v, par[v]) for v in V if par[v] is not None]
allrk = lambda V, rot: [(r, k) for r in V for k in range(len(rot[r]))]
cur = evaluate(V, rot, S, allrk(V, rot)); state = (V, rot, S)
for t in range(iters):
    m = mutate(*state)
    if m is None:
        continue
    rk = allrk(m[0], m[1])
    sample = rng.sample(rk, min(16, len(rk))) + [cur[1]] if cur[1] else rng.sample(rk, min(16, len(rk)))
    val = evaluate(*m, sample)
    if val[0] >= cur[0]:
        if val[0] > cur[0]:
            # full evaluation on improvement
            val = max(val, evaluate(*m, rk))
        cur = val; state = m
    if val[0] >= 9:
        break
V, rot, S = state
r, k = cur[1] if cur[1] else (V[0], 0)
par = parents(V, S, r)
res = H.check(V, rot, par, r, k, deep=True)
print('OBJ', OBJ, 'seed', seed, 'fam', fam, 'n', len(V), 'best', round(cur[0], 4), 'kind', res['kind'], 'j', res.get('j'), 'mx', {a: round(b, 3) for a, b in res['mx'].items()})
print('INSTANCE rot=', rot, 'S=', S, 'r=', r, 'k=', k)
