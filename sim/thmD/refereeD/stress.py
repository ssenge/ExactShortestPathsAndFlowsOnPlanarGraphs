import os
"""Stress the independent simulator on the driver's instance families.
Checks (all from the paper's text): (Comp) by construction, (Pieces), (Dist), (C23) on [j,i]/[i,k], the side rule, O(b),
and final value = min cut with repair, under reading from 0, random reading per annulus, both namings."""
import sys, random, collections, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD, sim, networkx as nx
start, N, tmax = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
C = collections.Counter(); st = collections.Counter(); bad = []
t0 = time.time()
for seed in range(start, start + N):
    if time.time() - t0 > tmax: break
    I = thmD.make_instance(seed)
    ends, cap = [tuple(e) for e in I['ends']], list(I['cap'])
    if any(u == v for u, v in ends): C['loops_skip'] += 1; continue
    if len({frozenset(e) for e in ends}) != len(ends): C['multi'] += 1
    n = I['n']; K = 19 * n + 1
    # theorem's lengths: w = K c' + 1, c' = n^2 c + 1 (without merging parallels: fine for the path structure)
    lw = lambda e: K * (n * n * cap[e] + 1) + 1
    In = sim.Inst(n, ends, I['rot'], cap, I['s'], I['t'])
    if In.euler() != 2: C['nonplanar_skip'] += 1; continue
    G = nx.Graph()
    for e, (u, v) in enumerate(ends):
        if G.has_edge(u, v): G[u][v]['capacity'] += cap[e]
        else: G.add_edge(u, v, capacity=cap[e])
    mc = nx.minimum_cut(G, I['s'], I['t'])[0]
    rng = random.Random(seed)
    f = rng.choice(sorted({In.corner_face(I['s'], k) for k in range(len(I['rot'][I['s']]))}))
    g = rng.choice(sorted({In.corner_face(I['t'], k) for k in range(len(I['rot'][I['t']]))}))
    cs = rng.choice([k for k in range(len(I['rot'][I['s']])) if In.corner_face(I['s'], k) == f])
    ct = rng.choice([k for k in range(len(I['rot'][I['t']])) if In.corner_face(I['t'], k) == g])
    for reading in ('0', 'random'):
        for flip in (False, True):
            try:
                R = sim.run(In, f, g, cs, ct, length=lw, repair=True, reading=reading, rng=rng, stats=st, flip=flip)
                Lam = min(r[1] for r in R['results'])
                val = (Lam // K) // (n * n)
                C['runs'] += 1
                if val != mc: C['wrong'] += 1; bad.append((seed, reading, flip, val, mc))
                R0 = sim.run(In, f, g, cs, ct, length=lw, repair=False, reading=reading, rng=rng, stats=collections.Counter(), flip=flip)
                if (min(r[1] for r in R0['results']) // K) // (n * n) != mc: C['wrong_norepair'] += 1
            except sim.Fail as ex:
                C['FAIL:' + str(ex).split(' t=')[0][:40]] += 1; bad.append((seed, reading, flip, str(ex)))
print('seeds', seed - start + 1, dict(C)); print(dict(st)); print('bad', bad[:12], 'time', round(time.time() - t0))
