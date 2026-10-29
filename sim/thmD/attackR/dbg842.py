import sys, os, collections, random, json
sys.path.insert(0, sys.argv[1])
import deep, defr
from deep import Run, make_instance
sd = int(sys.argv[2]); pol = sys.argv[3]
deep.FORCE.update(fam=sys.argv[4].split(','), scheme=sys.argv[5].split(','))
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
print('meta', meta, 'n', emb.n, 'm', emb.m, 's', s, 't', t, 'deg', emb.deg(s), emb.deg(t))
C = collections.Counter(); notes = []
orig_step = Run.step
def step(self, A, level):
    M = self.M
    j, k = A.j, A.k
    if k > j + 1:
        print('--- STEP level', level, 'aid', A.aid, 'j,k', j, k)
        for nm, ch in (('left', A.left), ('right', A.right)):
            if ch:
                print('   %s chord nodes' % nm, [(x, M.np[x].anc) for x in ch['nodes']])
                print('   %s chord edges' % nm, [(M.he[h1].dart>>1, M.he[h1].kind) for h1, h2 in ch['edges']])
    # capture P_i
    orig_pick = self.pick_path
    cap = {}
    def pick(nodes, src, tgt, wfun, prefer):
        r = orig_pick(nodes, src, tgt, wfun, prefer)
        cap['p'] = r
        if r[0]:
            print('   [pick] nodes+anc', [(x, M.np[x].anc, sum(1 for it in M.np[x].items if it[0]=='S')) for x in r[0]])
            print('   [pick] edges (prim, kind)', [(M.he[h].dart >> 1, M.he[h].kind) for h in r[1]])
        return r
    self.pick_path = pick
    ch = orig_step(self, A, level)
    self.pick_path = orig_pick
    if 'p' in cap and k > j + 1:
        pn, ph, L = cap['p']
        print('   P_i nodes', [(x, M.np[x].anc if x in M.np else 'split') for x in pn])
        print('   P_i edges', [(M.he[h].dart >> 1) for h in ph])
    post = getattr(A, 'post', None)
    if post:
        comp = post['comp']
        byc = collections.defaultdict(list)
        for z in post['newnodes']: byc[comp[z]].append(z)
        for c, zs in byc.items():
            ancs = sorted({M.np[z].anc for z in zs if M.np[z].anc[0]=='p'})
            isl = [cc.aid for cc in ch if set(zs) <= cc.nodes]
            hb = any(any(it[0]=='H' and deep.tok(M,it[1]) in post['badtok'] for it in M.np[z].items) for z in zs)
            print('   comp', c, 'size', len(zs), 'live', isl, 'hasbad', hb, 'P-anc', ancs)
        print('   badtok', post['badtok'])
    print('   children', [(c.aid, c.j, c.k) for c in ch], {k_: v for k_, v in self.C.items() if k_.startswith('child') or k_.startswith('orphan') or k_=='overlap'})
    return ch
Run.step = step
R = Run(emb, s, t, rng, pol, frozenset(), C, notes, dict(seed=sd))
R.run()
print('P faces', R.pf, 'P edges', R.pe, 'lam', R.lam, 'cuts', [(c['z'], c['i'], c['mode'], c['_e']) for c in R.cuts])
print('ends', emb.ends); print('rot', emb.rot); print('cap', emb.cap)
for n in notes: print(n)
