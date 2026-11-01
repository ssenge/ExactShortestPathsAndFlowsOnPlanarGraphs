import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv, gens
cnt = collections.Counter(); bad_any = collections.Counter(); ex = []
for sd in range(60):
    I = gens.make(sd)
    for r in range(3):
        ch = adv.Chooser(mode='policy', pols=list(adv.POLICIES), prng=random.Random(r), cnt=cnt)
        chk, info, bad = adv.run(I, adv.base_opts(pfar=0.5), random.Random(sd * 10 + r), ch, cnt, geo=True)
        for k in bad:
            bad_any[k] += 1
        if bad and len(ex) < 3:
            ex.append((sd, r, dict(chk.flags), [str(x)[:300] for x in chk.notes[:4]]))
print(dict(bad_any)); print(ex)
print({k: v for k, v in sorted(cnt.items()) if k.startswith('G_') or k in ('inc', 'both_bounds')})
