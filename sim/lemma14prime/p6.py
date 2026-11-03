"""Property 6 vs (G1'): K_{2,m} + chord uw.  Global BFS tree rooted at u (so uw is a tree edge) or at a petal.
Reports, per depth, the number of bags whose induced subgraph contains uw, and how many per-bag trees
T_X contain uw; runs all §3 checks on the same decomposition."""
import sys, os, json, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import PG, Fail
from geo import fam_k2m, virtual_candidates
from engine import Engine
import post

m = int(sys.argv[1]); root = sys.argv[2]; leaf = int(sys.argv[3]) if len(sys.argv) > 3 else 8
pos, E = fam_k2m(m, chord=True, sub=1, seed=1)
g = PG(pos, E, seed=1)
vc = virtual_candidates(pos, E)
cfg = dict(leaf=leaf, modes={'bal': 1}, swap=0.0, root=0 if root == 'u' else 2, tries=400, bal=0.95)
eng = Engine(g, vc, random.Random(5), cfg)
eng.run()
if len(sys.argv) <= 4: post.lemma16(eng); post.e2e(eng); post.walk(eng)
post.prop6(eng)
u, w = 0, 1
ch = g.e(u, w)
per = collections.Counter(); perT = collections.Counter(); perS = collections.Counter(); nb = collections.Counter()
for b, B in eng.bags.items():
    d = B['depth']; nb[d] += 1
    if u in B['X'] and w in B['X']:
        per[d] += 1
    if B.get('TX') and w in B['TX'].get(u, ()):
        perT[d] += 1
    if B.get('S') and u in B['S'] and w in B['S']:
        perS[d] += 1
n = g.n
print('n', n, 'D(diameter)', __import__('networkx').diameter(g.G), 'leaf', leaf, 'BFS root', root, 'chord in T:', eng.T.has_edge(u, w))
print('depth: #bags | #bags with u,w (chord in G[X]) | #non-leaf bags whose T_X contains uw | #separators through u and w')
for d in sorted(nb):
    print(d, nb[d], per[d], perT[d], perS[d])
print('max bags with chord at one depth', max(per.values()), ' max T_X containing chord', max(perT.values()) if perT else 0)
print('virtual closings', eng.st['virtual_closings'], 'fails', eng.fails[:3])
print('checks', {k: v for k, v in eng.st.items() if k in ('G1_checks', 'tiles_checked', 'monge_ineqs', 'L16_checks', 'e2e_gluings', 'walk_rebuilds', 'hub_checks')})
