import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv, gens, geo
orig_init = geo.Geo.__init__
def swapped(self, emb, s, t, cnt, flag):
    orig_init(self, emb, t, s, cnt, flag)
orig_pc = geo.Geo.pos_cut
for name, patch in (('swap_s_t', ('init', swapped)), ('shift_cut', ('pc', lambda self, d: orig_pc(self, d) + 1))):
    if patch[0] == 'init':
        geo.Geo.__init__ = patch[1]
    else:
        geo.Geo.pos_cut = patch[1]
    bad_any = collections.Counter(); cnt = collections.Counter()
    for sd in range(20):
        I = gens.make(sd)
        ch = adv.Chooser(mode='policy', pols=['rand'], prng=random.Random(0), cnt=cnt)
        chk, info, bad = adv.run(I, adv.base_opts(), random.Random(sd), ch, cnt, geo=True)
        for k in bad: bad_any[k] += 1
    print(name, dict(bad_any), cnt['G_inc'])
    geo.Geo.__init__ = orig_init; geo.Geo.pos_cut = orig_pc
