"""Smallest SIMPLE instances (no parallel edges: the graph after the merge step) for the phenomena seen on multigraphs.
Usage: python3 -I scan_simple.py OUT.json MAXSEC"""
import sys, os, json, time, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
import nd_core as X, nd_drive as D, nd_fam as F
out, maxsec = sys.argv[1], float(sys.argv[2])
maps = json.load(open(D.MAPS))
ctx = X.Ctx()
t0 = time.time()
for M in range(3, 9):
    for mi, (n, ends, rot) in enumerate(maps[str(M)]):
        if len({frozenset(e) for e in ends}) != len(ends):
            continue
        if time.time() - t0 > maxsec:
            break
        rng = random.Random(mi)
        for cap in ([1] * M, [rng.randint(1, 2) for _ in range(M)], [rng.randint(1, 3) for _ in range(M)], [rng.randint(0, 2) for _ in range(M)]):
            for s, t in itertools.permutations(range(n), 2):
                I = X.Inst(n, [tuple(e) for e in ends], rot, cap, s, t, tag='simple%d:%d' % (M, mi))
                for f, g, cs, ct in D.all_choices(I):
                    D.enum_run(I, ctx, f, g, cs, ct, 30, dict(cap_b=2, cap_paths=32, c_stats=True, ghat=False))
    print(M, sorted(ctx.examples), ctx.C['runs'], round(time.time() - t0), flush=True)
k = 0
while time.time() - t0 < maxsec:
    I, rng = F.make(k * 7 + 5, None, 14)
    k += 1
    if len({frozenset(e) for e in I.ends}) != I.m:
        continue
    for r in range(4):
        f, g, cs, ct = D.random_choice(I, rng)
        R = X.Run(I, ctx, X.PolicyCh(rng, rng.choice(D.POLS)), f, g, cs, ct, dict(cap_b=2, cap_paths=24, sample=True, c_stats=True, ghat=False))
        try:
            R.go()
        except X.Abort:
            ctx.C['abort'] += 1
json.dump(dict(examples=ctx.examples, fails=ctx.fails, runs=ctx.C['runs'], counts=dict(ctx.C)), open(out, 'w'), default=str)
print('runs', ctx.C['runs'], 'fails', {k: v for k, v in ctx.C.items() if k.startswith('FAIL')})
for k, v in sorted(ctx.examples.items()):
    print(k, v['size'], json.dumps(v['inst']), v['f'], v['g'], v['cs'], v['ct'], v['seq'], v['level'], v['detail'][:300])
