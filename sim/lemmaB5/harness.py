"""Run mine.run and the reference b5.b5 on the same instance and compare."""
import sys, os, collections
sys.dont_write_bytecode = True
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 's9')
sys.path.insert(0, REPO)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b5 as REF
from mine import run, Fail, mkidx, tpath, sides_indep, random_virtual_marks, corner_faces, is_planar_rot

TOT = collections.Counter()
MX = {}


def upd(key, val, f=max):
    MX[key] = val if key not in MX else f(MX[key], val)


def check(V, rot, par, r, k, deep=True, cmp=True, tag=''):
    idx = mkidx(rot)
    n = len(V)
    res = run(V, rot, idx, par, r, k, deep=deep)
    for a, b in res['st'].items():
        TOT[a] += b
    for a, b in res['mx'].items():
        upd(a, b, min if 'min' in a else max)
    TOT['inst'] += 1; TOT['kind_' + res['kind']] += 1
    big = max(res['ins'], res['out'])
    upd('side_over_n', big / n)
    upd('side_over_n_n>=10' if n >= 10 else 'side_over_n_small', big / n)
    upd('S_over_2h1', len(res['cyc']) / (2 * res['h'] + 1))
    upd('max_chord_steps_one_walk', res['st'].get('chord_steps', 0))
    upd('max_e0_steps', res['st'].get('e0_steps', 0))
    if cmp:
        depth = {v: len(tpath(par, v, r)) - 1 for v in V}
        children = {v: set() for v in V}
        for v in V:
            if par[v] is not None:
                children[par[v]].add(v)
        try:
            ref = REF.b5(V, rot, idx, par, depth, children, r, k)
        except REF.Bad as ex:
            raise Fail('REF raised Bad: %s' % ex)
        if ref['kind'] != res['kind']:
            raise Fail('MISMATCH kind %s vs %s' % (ref['kind'], res['kind']))
        if {ref['x'], ref['z']} != {res['x'], res['z']} or sorted((ref['ins'], ref['out'])) != sorted((res['ins'], res['out'])):
            raise Fail('MISMATCH result ref %s vs mine %s' % ((ref['x'], ref['z'], ref['ins'], ref['out']), (res['x'], res['z'], res['ins'], res['out'])))
        if res['kind'] == 'virt' and (ref['cx'] != res['cx'] or ref['cz'] != res['cz']):
            raise Fail('MISMATCH corners')
        # reference side counter on the final answer
        cyc = REF.path(par, depth, ref['x'], ref['z'])
        if ref['kind'] == 'virt':
            cA, cB = REF.count_sides(V, rot, cyc, ref['cx'][1], ref['cz'][1])
        else:
            cA, cB = REF.count_sides(V, rot, cyc, None, None)
        if isinstance(cA, (set, frozenset, list)):
            # newer b5.py returns the two vertex sets; compare them with mine as sets too
            A_, B_ = set(cA), set(cB)
            cA, cB = len(A_), len(B_)
            if A_ & set(cyc) or B_ & set(cyc) or A_ & B_:
                raise Fail('ref sides overlap the cycle')
        if sorted((cA, cB)) != sorted((res['ins'], res['out'])):
            raise Fail('MISMATCH ref count_sides %s vs %s' % ((cA, cB), (res['ins'], res['out'])))
        TOT['ref_cmp'] += 1
    return res


def report():
    print(dict(TOT))
    print({a: (round(b, 4) if isinstance(b, float) else b) for a, b in MX.items()})
