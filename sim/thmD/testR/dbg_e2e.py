"""trace an e2e_value failure: per annulus, the c-distance p_t^0 -> p_t^1 inside it for every t.
usage: python3 -I dbg_e2e.py SEED [var] [fams] [schemes] [policy-override]"""
import sys, os, collections, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deep
from deep import Run, make_instance, INF
sd = int(sys.argv[1])
var = frozenset(sys.argv[2].split(',')) if len(sys.argv) > 2 and sys.argv[2] else frozenset()
if len(sys.argv) > 3 and sys.argv[3]:
    deep.FORCE['fam'] = sys.argv[3].split(',')
if len(sys.argv) > 4 and sys.argv[4]:
    deep.FORCE['scheme'] = sys.argv[4].split(',')
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
pol = rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c', 'kiss', 'kiss_c'])
if len(sys.argv) > 5:
    pol = sys.argv[5]
print('meta', meta, 'pol', pol, 'n', emb.n, 'm', emb.m, 's', s, 't', t)
C = collections.Counter(); notes = []
orig_step = Run.step
def step(self, A, level):
    M = self.M
    cw = lambda e: self.emb.cap[e]
    row = []
    for tt in range(min(A.j, A.k), max(A.j, A.k) + 1):
        a, b = self.find_piece(A, (tt, 0)), self.find_piece(A, (tt, 1))
        if a is None or b is None:
            row.append((tt, None))
            continue
        d, _ = self.sssp(A.nodes, a, cw)
        row.append((tt, d.get(b, INF)))
    nres = len(self.results)
    ch = orig_step(self, A, level)
    print('L%d aid %d parent %s j,k=%d,%d nodes %d  dist_c(t)=%s  results+=%s  children=%s' % (
        level, A.aid, A.parent.aid if A.parent else None, A.j, A.k, len(A.nodes), row,
        self.results[nres:], [(c.aid, c.j, c.k) for c in ch]))
    return ch
Run.step = step
orig_mk = Run.mk_orphan
def mk(self, newnodes, comp, c, jj, kk, A, why):
    O = orig_mk(self, newnodes, comp, c, jj, kk, A, why)
    cw = lambda e: self.emb.cap[e]
    row = []
    for tt in range(min(jj, kk), max(jj, kk) + 1):
        a, b = self.find_piece(O, (tt, 0)), self.find_piece(O, (tt, 1))
        if a is not None and b is not None:
            d, _ = self.sssp(O.nodes, a, cw)
            row.append((tt, d.get(b, INF)))
    print('   ORPHAN from aid %d why %s range %d,%d nodes %d dist_c=%s' % (A.aid, why, jj, kk, len(O.nodes), row))
    return O
Run.mk_orphan = mk
R = Run(emb, s, t, rng, pol, var, C, notes, dict(seed=sd))
R.run()
print('lambda', R.lam, 'P faces', R.pf, 'P edges', R.pe, 'cuts', [(c['z'], c['i'], c['mode']) for c in R.cuts])
print('BAD', {k: v for k, v in C.items() if k.startswith('BAD')})
for n in notes: print(n)
