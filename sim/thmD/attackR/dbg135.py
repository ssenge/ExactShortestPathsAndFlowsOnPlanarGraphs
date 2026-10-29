import sys, os, collections, random, json
sys.path.insert(0, sys.argv[1])
import deep
from deep import Run, make_instance
sd = int(sys.argv[2]); pol = sys.argv[3]
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
pol2 = rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c'])
print('meta', meta, 'pol drawn', pol2, 'n', emb.n, 'm', emb.m, 's', s, 't', t)
C = collections.Counter(); notes = []
# instrument step
orig_step = Run.step
def step(self, A, level):
    ch = orig_step(self, A, level)
    post = getattr(A, 'post', None)
    print('STEP level', level, 'aid', A.aid, 'j,k', A.j, A.k, 'children', [(c.aid, c.j, c.k) for c in ch])
    for k_, v in sorted(self.C.items()):
        if k_.startswith('child_') : print('   ', k_, v)
    return ch
Run.step = step
R = Run(emb, s, t, rng, pol2, frozenset(), C, notes, dict(seed=sd))
R.run()
print('P faces', R.pf, 'P edges', R.pe, 'lam', R.lam, 'cuts', [(c['z'], c['i'], c['mode']) for c in R.cuts])
for n in notes: print(n)
print({k: v for k, v in C.items() if k.startswith('BAD') or k.startswith('child')})
