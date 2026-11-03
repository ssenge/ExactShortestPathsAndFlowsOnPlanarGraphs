"""Counterexample search for [8] Claim 4.6 ('S[X_i^-] forms a connected segment', '(T' u S)[X_i^-] connected')
and the step of [8] Lemma 4.7 ('T[X'] has at most one more component than T[X]').
LP-faithful children: z only inherited from S of ancestors, X+ = bounded side, T' = T[X] + connecting edges,
real closing edges only, and every separator encloses no vertex outside its bag (no hole swallowed)."""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx
from core import PG, pip
from geo import FAMS
from engine import Engine

class E2(Engine):
    def analyse(self, X, Xl, q, swap):
        r = super().analyse(X, Xl, q, swap)
        if r is None: return None
        others = [v for v in range(self.g.n) if v not in X]
        if others and pip(self.g.pos[others], self.g.pos[q]).any():
            return None            # S would enclose a hole of G[X]
        return r
    def lp46(self, b, res):
        super().lp46(b, res)
        q = res['q']; TX = res['TX']; X = self.bags[b]['X']
        for i, Y in enumerate(res['kids'][1:], 1):
            H = nx.Graph(); H.add_nodes_from(Y)
            for v in Y:
                for u in TX[v]:
                    if u in Y: H.add_edge(u, v)
            L = len(q)
            for k in range(L):
                if q[k] in Y and q[(k + 1) % L] in Y: H.add_edge(q[k], q[(k + 1) % L])
            if not nx.is_connected(H) and not hasattr(self, 'found'):
                self.found = dict(bag=b, depth=self.bags[b]['depth'], X=len(X), q=q, Y=sorted(Y),
                                  arcs=[[v for v in q if v in Y]], comps=[sorted(c) for c in nx.connected_components(H)],
                                  cX=self.comps_T(X), cY=self.comps_T(Y), real=res['real'],
                                  zX=sorted(self.bags[b]['z']))

fam = sys.argv[1]; best = None
for seed in range(int(sys.argv[2])):
    for size in ([dict(R=3, K=8), dict(R=4, K=10), dict(R=4, K=12), dict(R=5, K=14)] if fam == 'nested'
                 else [dict(n=30), dict(n=45), dict(n=60), dict(n=90)]):
        pos, E = FAMS[fam](seed, size)
        g = PG(pos, E, seed=seed)
        eng = E2(g, set(), random.Random(seed), dict(leaf=6, modes={'bal': 3, 'bnd': 1, 'onG': 2, 'rand': 1},
                                                    zall=0.0, swap=0.0, txmode='bfs', tries=150, degenerate=False))
        eng.run()
        if hasattr(eng, 'found') and (best is None or g.n < best[0]):
            best = (g.n, seed, size, eng.found)
        if best: break
print('smallest:', best[0], 'vertices; seed', best[1], best[2])
for k, v in best[3].items(): print(' ', k, v)
