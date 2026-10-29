"""print P_i of each step with P-ancestry, and a shortest c-path for the optimal t in each annulus.
usage: python3 -I dbg_e2e2.py SEED [fams] [schemes] [policy]"""
import sys, os, collections, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deep
from deep import Run, make_instance, INF
sd = int(sys.argv[1])
if len(sys.argv) > 2 and sys.argv[2]:
    deep.FORCE['fam'] = sys.argv[2].split(',')
if len(sys.argv) > 3 and sys.argv[3]:
    deep.FORCE['scheme'] = sys.argv[3].split(',')
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
pol = rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c', 'kiss', 'kiss_c'])
if len(sys.argv) > 4:
    pol = sys.argv[4]
C = collections.Counter(); notes = []
def lab(M, x):
    an = M.np[x].anc
    return 'p%d^%d' % (an[1], an[2]) if an[0] == 'p' else 'f%d' % M.np[x].face
orig_pick = Run.pick_path
def pick(self, nodes, src, tgt, wfun, prefer):
    r = orig_pick(self, nodes, src, tgt, wfun, prefer)
    M = self.M
    if r[0] and hasattr(self, 'cuts'):
        print('   path', ' '.join(lab(M, x) for x in r[0]), ' c-edges', [(M.he[h].dart >> 1, self.emb.cap[M.he[h].dart >> 1]) for h in r[1]], 'w', r[2])
    return r
Run.pick_path = pick
orig_step = Run.step
def step(self, A, level):
    M = self.M
    cw = lambda e: self.emb.cap[e]
    pl = sorted({lab(M, x) for x in A.nodes if M.np[x].anc[0] == 'p'}, key=lambda z: (int(z[1:].split('^')[0]), z))
    print('L%d aid %d j,k=%d,%d  P-copies in A: %s' % (level, A.aid, A.j, A.k, ' '.join(pl)))
    # optimal t in A
    best = None
    for tt in range(min(A.j, A.k), max(A.j, A.k) + 1):
        a, b = self.find_piece(A, (tt, 0)), self.find_piece(A, (tt, 1))
        if a is None or b is None:
            continue
        d, _ = self.sssp(A.nodes, a, cw)
        if best is None or d.get(b, INF) < best[0]:
            best = (d.get(b, INF), tt, a, b)
    if best:
        sv = self.policy
        self.policy = 'random'
        print('  best t=%d c=%d; a shortest c path:' % (best[1], best[0]))
        orig_pick(self, A.nodes, best[2], best[3], cw, set()) and None
        r = orig_pick(self, A.nodes, best[2], best[3], cw, set())
        print('   opt ', ' '.join(lab(M, x) for x in r[0]), [(M.he[h].dart >> 1) for h in r[1]])
        self.policy = sv
    print('  step:')
    ch = orig_step(self, A, level)
    print('  -> children', [(c.aid, c.j, c.k) for c in ch])
    return ch
Run.step = step
R = Run(emb, s, t, rng, pol, frozenset(), C, notes, dict(seed=sd))
R.run()
print('meta', meta, 'pol', pol, 'n', emb.n, 'm', emb.m, 's', s, 't', t, 'lambda', R.lam)
print('P faces', R.pf, 'P edges', R.pe)
print('BAD', {k: v for k, v in C.items() if k.startswith('BAD')})
