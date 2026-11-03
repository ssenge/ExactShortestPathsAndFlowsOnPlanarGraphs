"""Exhaustive-ish run of Lemma N on all connected planar graphs from the atlas (n<=Nmax), all rotations (capped),
all ordered s,t, shortest paths, both E_C end rules; pipeline on a sample."""
import sys, os, random, collections, json, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
import nlem

nmax = int(sys.argv[1])
pipe_rate = float(sys.argv[2])
secs = float(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
rng = random.Random(seed)
st = collections.Counter()
fails = []


def fail(msg, g, R):
    fails.append((msg, g.rot, R))
    if len(fails) < 8:
        print('FAIL', msg, g.rot, R, flush=True)


t0 = time.time()
ngraph = 0
for H in graph_atlas_g():
    if time.time() - t0 > secs:
        break
    if H.number_of_nodes() < 3 or H.number_of_nodes() > nmax or not nx.is_connected(H):
        continue
    if not nx.check_planarity(H)[0]:
        continue
    ngraph += 1
    for g in nlem.planar_rotations(H, rng, 4000):
        st['rotations'] += 1
        for s in H.nodes():
            for t in H.nodes():
                if s == t:
                    continue
                for R in nlem.shortest_paths(H, s, t):
                    for end in ('larger', 'smaller'):
                        res = nlem.check_structure(g, R, st, end, rng, fail)
                        if res is None:
                            continue
                        N, q, D, dN = res
                        if end == 'larger':
                            cc = nlem.caps(g, rng)
                            P = [x for x in q if x[0] == 'c']
                            if rng.random() < pipe_rate * 5:
                                nlem.lam_exact(cc, g, N, len(N.nodes), P, None, st, fail, 'metric')
                            if rng.random() < pipe_rate:
                                nm = rng.choice(['lo', 'hi', 'two', 'rand', 'blo', 'bhi', 'btwo', 'brand'])
                                nlem.pipeline(g, N, q, cc, s, t, st, fail, nm, rng)
    st['graphs'] = ngraph
print(json.dumps(st, sort_keys=True))
print('secs', round(time.time() - t0), 'fails', len(fails))
