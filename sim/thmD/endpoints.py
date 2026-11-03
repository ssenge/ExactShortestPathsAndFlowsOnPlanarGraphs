"""The endpoint cases of [18, Remark 3.3] on the smallest graphs, literal graph against the repaired one.

Runs thmD.py (imported, not modified) on every planar rotation of three fixed instances, over run seeds that vary
f, g and the corners, and counts the runs in which the literal graph gives a wrong cut value or fails its structural
checks. Then it measures, on random instances, how often the formula of Remark 3.3 does not fit the edge chosen at s or t
(the driver then takes the mirrored copy and flags dev_mirrored_endpoint).

usage: python3 -I endpoints.py [sweep]        (default 300 random instances)
"""
import sys, os, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD

SWEEP = int(sys.argv[1]) if len(sys.argv) > 1 else 300


def rotations(n, ends):
    """All rotation systems with the first dart of each vertex fixed; planar ones are kept by the caller."""
    at = [[] for _ in range(n)]
    for e, (u, v) in enumerate(ends):
        at[u].append(2 * e); at[v].append(2 * e + 1)
    for choice in itertools.product(*[[[a[0]] + list(p) for p in itertools.permutations(a[1:])] for a in at]):
        yield [list(c) for c in choice]


def run(name, n, ends, cap, s, t, runs, pfars, offset=0):
    """Run seeds are 7919 r + offset + int(pfar); the offsets below reproduce the counts quoted in the README."""
    out = {}
    for variant in ('literal', 'fixed'):
        C = collections.Counter(); nrot = 0
        for rot in rotations(n, ends):
            if not thmD.Builder(n, ends, rot).euler_ok():
                continue
            nrot += 1
            I = dict(n=n, ends=ends, rot=rot, cap=cap, s=s, t=t)
            for r in range(runs):
                for pfar in pfars:
                    opts = dict(mode='claimed', variant=variant, tiebreak='minid', pairs=1, pcommon=0.5, pfar=pfar,
                                e0rule='formal', ends=0)
                    chk, info = thmD.run_one(I, opts, 7919 * r + offset + int(pfar))
                    same = info.get('eps', {}).get('e0') == info.get('ept', {}).get('e0')
                    bad = 'iv_value' in chk.flags or 'fail_exception' in chk.flags
                    C['runs'] += 1; C['e0 = elast'] += same; C['wrong'] += bad
                    C['wrong with e0 = elast'] += bad and same
                    C['wrong with later incision through e0 or elast'] += bad and not same
        out[variant] = dict(C)
        print('%-9s %-7s embeddings %d  %s' % (name, variant, nrot, dict(C)))
    assert out['fixed']['wrong'] == 0, 'the repaired graph must never fail'
    return out


if __name__ == '__main__':
    # D1: a later incision through e_last joins the two sides of the endpoint split at t; minimum cut 2, reported 0
    w4 = run('square+2', 4, [(0, 3), (0, 1), (1, 2), (2, 3), (3, 1)], [1, 1, 1, 1, 5], 1, 2, 60, (0.5,), offset=1)
    # D2: e_0 = e_last is the edge st; the two endpoint rules change the copies of the same edge
    tri = run('triangle', 3, [(0, 1), (0, 2), (1, 2)], [3, 1, 1], 0, 1, 40, (0.0, 1.0))
    sq = run('sq+diag', 4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)], [1, 1, 1, 1, 3], 0, 2, 40, (0.0, 1.0))
    assert w4['literal']['wrong'] > 0 and tri['literal']['wrong'] > 0 and sq['literal']['wrong'] > 0
    assert tri['literal']['wrong'] == tri['literal']['wrong with e0 = elast']
    # D3: how often the formula of Remark 3.3 does not fit the chosen edge
    C = collections.Counter()
    for sd in range(SWEEP):
        I = thmD.make_instance(sd)
        chk, info = thmD.run_one(I, dict(mode='claimed', variant='fixed', tiebreak='minid', pairs=1, pcommon=0.5,
                                         pfar=0.5, e0rule='formal', ends=1), sd)
        C['instances'] += 1
        C['mirrored copy needed'] += 'dev_mirrored_endpoint' in chk.flags
        C['wrong'] += 'iv_value' in chk.flags
    print('random instances, repaired graph:', dict(C))
    assert C['wrong'] == 0
