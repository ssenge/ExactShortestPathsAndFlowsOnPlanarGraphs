"""trace the minimized counterexample: python3 -I trace_min.py logs/min_simple0.json"""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import minimize_e2e as ME
from deep import Run, INF
d = json.load(open(sys.argv[1]))
I = d['instance']
w = d['witnesses'][0]
emb = ME.mk(I)
def lab(M, x):
    an = M.np[x].anc
    return 'p%d^%d' % (an[1], an[2]) if an[0] == 'p' else 'f%d' % M.np[x].face
orig_pick = Run.pick_path
def pick(self, nodes, src, tgt, wfun, prefer):
    r = orig_pick(self, nodes, src, tgt, wfun, prefer)
    if r[0] and getattr(self, 'cuts', None):
        M = self.M
        print('    path', ' '.join(lab(M, x) for x in r[0]), '| edges', [M.he[h].dart >> 1 for h in r[1]],
              '| c', sum(self.emb.cap[M.he[h].dart >> 1] for h in r[1]))
    return r
Run.pick_path = pick
orig_step = Run.step
def step(self, A, level):
    M = self.M
    cw = lambda e: self.emb.cap[e]
    pl = sorted({lab(M, x) for x in A.nodes if M.np[x].anc[0] == 'p'}, key=lambda z: (int(z[1:].split('^')[0]), z))
    row = []
    for tt in range(min(A.j, A.k), max(A.j, A.k) + 1):
        a, b = self.find_piece(A, (tt, 0)), self.find_piece(A, (tt, 1))
        if a is not None and b is not None:
            dd, _ = self.sssp(A.nodes, a, cw)
            row.append((tt, dd.get(b, INF)))
    print('L%d annulus (%d,%d): P-copies %s; d_c(p_t^0,p_t^1) in A: %s' % (level, A.j, A.k, ' '.join(pl), row))
    n0 = len(self.results)
    ch = orig_step(self, A, level)
    print('    computed', [(t, c) for (t, L, c) in self.results[n0:]], '-> children', [(c.j, c.k) for c in ch])
    return ch
Run.step = step
orig_mk = Run.mk_orphan
def mk(self, newnodes, comp, c, jj, kk, A, why):
    O = orig_mk(self, newnodes, comp, c, jj, kk, A, why)
    print('    side (%d,%d) not recursed (%s); P-copies %s' % (jj, kk, why, ' '.join(sorted(lab(self.M, x) for x in O.nodes if self.M.np[x].anc[0] == 'p'))))
    return O
Run.mk_orphan = mk
C = collections.Counter()
R = Run(emb, I['s'], I['t'], random.Random(1), 'random', frozenset(), C, [], {})
R.force_fg, R.force_cuts = tuple(w['fg']), tuple(tuple(c) for c in w['cuts'])
R.run()
print('lambda', R.lam, 'reported', min(r[2] for r in R.results), 'P faces', R.pf, 'P edges', R.pe,
      'nonunique picks', R.nonunique, 'BAD', {k: v for k, v in C.items() if k.startswith('BAD')})
# the dual edges of P and the min cut
print('faces', {f: [(d >> 1) for d in emb.faces[f]] for f in range(len(emb.faces))})
