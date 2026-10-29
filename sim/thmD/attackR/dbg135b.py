import sys, os, collections, random, json
sys.path.insert(0, sys.argv[1])
import deep, defr
from deep import Run, make_instance
sd = int(sys.argv[2])
emb, s, t, meta = make_instance(sd)
rng = random.Random(sd * 7919 + 13)
pol2 = rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c'])
C = collections.Counter(); notes = []
orig_step = Run.step
def step(self, A, level):
    M = self.M
    j, k = A.j, A.k
    if k > j + 1:
        print('--- STEP level', level, 'aid', A.aid, 'j,k', j, k)
        print('   annulus P-nodes:', sorted(M.np[x].anc for x in A.nodes if M.np[x].anc[0]=='p'))
        if A.left: print('   left chord nodes anc', [M.np[x].anc for x in A.left['nodes']])
        if A.right: print('   right chord nodes anc', [M.np[x].anc for x in A.right['nodes']])
    ch = orig_step(self, A, level)
    post = getattr(A, 'post', None)
    if post:
        comp = post['comp']
        byc = collections.defaultdict(list)
        for z in post['newnodes']: byc[comp[z]].append(z)
        live = {c.aid: c for c in ch}
        for c, zs in byc.items():
            ancs = sorted({M.np[z].anc for z in zs if M.np[z].anc[0]=='p'})
            isl = [cc.aid for cc in ch if set(zs) <= cc.nodes]
            hb = any(any(it[0]=='H' and deep.tok(M,it[1]) in post['badtok'] for it in M.np[z].items) for z in zs)
            print('   comp', c, 'size', len(zs), 'live', isl, 'hasbad', hb, 'P-anc', ancs)
    return ch
Run.step = step
orig_check = Run.check_level
def check_level(self, G, prevG, active, level, I):
    comp = defr.token_components(G)
    print('=== LEVEL', level, 'token components', len(set(comp)), 'active', [(a.aid, a.j, a.k) for a in active])
    return orig_check(self, G, prevG, active, level, I)
Run.check_level = check_level
R = Run(emb, s, t, rng, pol2, frozenset(), C, notes, dict(seed=sd))
R.run()
for n in notes: print(n)
