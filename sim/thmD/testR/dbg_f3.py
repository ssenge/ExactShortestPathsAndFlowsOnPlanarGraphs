"""print the step where F3 (either reading) mismatches. usage: SEED var [fams] [schemes]"""
import sys, os, collections, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deep
from deep import Run, make_instance, INF
sd = int(sys.argv[1])
var = frozenset(sys.argv[2].split(',')) if sys.argv[2] else frozenset()
if len(sys.argv) > 3 and sys.argv[3]:
    deep.FORCE['fam'] = sys.argv[3].split(',')
if len(sys.argv) > 4 and sys.argv[4]:
    deep.FORCE['scheme'] = sys.argv[4].split(',')
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
pol = rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c', 'kiss', 'kiss_c'])
C = collections.Counter(); notes = []
def lab(M, x):
    an = M.np[x].anc
    return ('p%d^%d' % (an[1], an[2]) if an[0] == 'p' else 'f%d' % M.np[x].face) + '#%d' % x
orig_pick = Run.pick_path
def pick(self, nodes, src, tgt, wfun, prefer):
    r = orig_pick(self, nodes, src, tgt, wfun, prefer)
    self._last = r
    return r
Run.pick_path = pick
orig_step = Run.step
def step(self, A, level):
    M = self.M
    before = {k: v for k, v in self.C.items() if 'F3' in k}
    desc = dict(L=level, aid=A.aid, jk=(A.j, A.k), parent=A.parent.aid if A.parent else None,
                nodes=sorted(lab(M, x) for x in A.nodes))
    chords = {}
    for nm in ('left', 'right', 'leftF', 'rightF'):
        ch = getattr(A, nm, None)
        chords[nm] = (None if not ch else (' '.join(lab(M, x) for x in ch['nodes']),
                      [(M.he[h1].dart >> 1, M.he[h1].kind) for h1, h2 in ch['edges']]))
    ch = orig_step(self, A, level)
    after = {k: v for k, v in self.C.items() if 'F3' in k}
    if after != before:
        print('F3 change', {k: after[k] - before.get(k, 0) for k in after})
        print(desc)
        for k, v in chords.items(): print('  ', k, v)
        pn, ph, L = self._last
        print('  P_i', ' '.join(lab(M, x) if x in M.np else str(x) for x in pn), [(M.he[h].dart >> 1, M.he[h].kind) if h in M.he else h for h in ph])
        post = A.post
        comp = post['comp']
        byc = collections.defaultdict(list)
        for z in post['newnodes']: byc[comp[z]].append(z)
        for c, zs in byc.items():
            print('   comp', c, 'live', [cc.aid for cc in ch if set(zs) <= cc.nodes], sorted(lab(M, z) for z in zs))
        print('   badtok c', post['badtok'], ' f', post['badtok_f'])
    return ch
Run.step = step
R = Run(emb, s, t, rng, pol, var, C, notes, dict(seed=sd))
R.run()
print('meta', meta, 'pol', pol, 'n', emb.n, 'm', emb.m, 's', s, 't', t, 'lam', R.lam)
print('P faces', R.pf, 'P edges', R.pe, 'cuts', [(c['z'], c['i'], c['mode']) for c in R.cuts])
print('ends', emb.ends); print('rot', emb.rot); print('cap', emb.cap)
for n in notes: print(n)
