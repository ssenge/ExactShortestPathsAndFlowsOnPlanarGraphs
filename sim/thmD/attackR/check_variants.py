"""For each e2e counterexample, rerun every failing (f, g, corners) choice under driver variants:
'' (driver), lit_chord, lit_full (live = no bad edge, recurse also on empty ranges as leaves),
clamp (i1, i2 clamped to [j, k]). Prints how many choices still miss lambda.
usage: python3 -I check_variants.py HITS.json [MAXHITS]"""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import minimize_e2e as ME
from deep import Run


def run(I, fg, cuts, var):
    emb = ME.mk(I)
    C = collections.Counter()
    R = Run(emb, I['s'], I['t'], random.Random(1), 'random', frozenset(var), C, [], {})
    R.force_fg, R.force_cuts = fg, cuts
    R.run()
    got = min((r[2] for r in R.results), default=None)
    other = sorted(k for k in C if k.startswith('BAD_') and not k.startswith('BAD_e2e'))
    return got, R.lam, other


hits = json.load(open(sys.argv[1]))
hits = hits['hits'] if 'hits' in hits else [dict(hits['instance'])]
for h in hits[:int(sys.argv[2]) if len(sys.argv) > 2 else None]:
    I = dict(n=h['n'], ends=[tuple(e) for e in h['ends']], rot=h['rot'], cap=h['cap'], s=h['s'], t=h['t'])
    W, tot = ME.witnesses(I, first_only=False)
    res = collections.Counter()
    for w in W:
        fg, cuts = tuple(w['fg']), tuple(tuple(c) for c in w['cuts'])
        for var in ((), ('lit_chord',), ('lit_full',), ('clamp',)):
            got, lam, other = run(I, fg, cuts, var)
            res[('+'.join(var) or 'driver', 'miss' if got != lam else 'ok')] += 1
            for o in other:
                res[('+'.join(var) or 'driver', o)] += 1
    print(json.dumps(dict(seed=h.get('seed'), n=I['n'], m=len(I['ends']), choices=tot, failing=len(W),
                          variants={'%s:%s' % k: v for k, v in sorted(res.items())})))
