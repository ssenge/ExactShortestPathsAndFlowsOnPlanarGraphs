"""Run the author's Reif driver (sim/thmD/thmD.py, imported read-only, not modified) on the
instances where my simulation of [18, Alg. 3] misses lambda, over many run seeds (f, g, corners).
usage: python3 -I confirm_author.py HITS.json NRUNS [variant]"""
import sys, os, json, collections
THMD = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, THMD)
import thmD

hits = json.load(open(sys.argv[1]))['hits']
nruns = int(sys.argv[2])
variant = sys.argv[3] if len(sys.argv) > 3 else 'fixed'
for h in hits:
    I = dict(n=h['n'], ends=[tuple(e) for e in h['ends']], rot=h['rot'], cap=h['cap'], s=h['s'], t=h['t'])
    C = collections.Counter()
    ex = None
    for r in range(nruns):
        for pfar in (1.0, 0.0):
            opts = dict(mode='claimed', variant=variant, tiebreak='minid', pairs=1, pcommon=0.0, pfar=pfar,
                        e0rule='formal')
            chk, info = thmD.run_one(I, opts, 7919 * r + int(pfar))
            C['runs'] += 1
            for k in chk.flags:
                C[k] += 1
            if 'iv_value' in chk.flags and ex is None:
                ex = dict(run=r, pfar=pfar, reported=info.get('reported'), mincut=info.get('mincut'),
                          pf=info.get('pf'), P_edges=info.get('Pedges'), eps=info.get('eps'), ept=info.get('ept'),
                          i12_outside=info.get('i12_outside'), child_range_empty=info.get('child_range_empty'))
    print(json.dumps(dict(seed=h['seed'], n=h['n'], m=h['m'], lam=h['lam'], mine=h['got'],
                          author_flags=dict(C), first_iv_value=ex), default=str))
