"""Greedy minimiser for a failing instance. Oracle: some run of the recursion on the instance
fails with a flag starting with one of CLASS (explore() over all choice sequences up to MAXRUNS,
then 60 random policy runs). Steps: delete an edge (keep connected), contract an edge, set a
capacity to 0, 1 or half. Reports the minimum cut of the result by networkx.

Usage: python3 -I minimize.py IN.json OUT.json [flagclass,...] [maxruns]
IN.json: {"I": instance} (a fails entry of run_adv / hill / run_exh) or an instance.
"""
import sys
import os
import json
import random
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv

T = adv.T
GEO = os.environ.get('GEO') == '1'


def failing(I, cls, maxruns):
    n, comp, fl = adv.explore(I, adv.base_opts(), max_runs=maxruns, stop_on_fail=True, geo=GEO)
    for f in fl:
        if any(k.startswith(cls) for k in f['flags'] if not k.startswith(adv.IGNORE)):
            return ('explore', f['prefix'], f['flags'])
    rng = random.Random(1)
    for r in range(60):
        cnt = collections.Counter()
        ch = adv.Chooser(mode='policy', pols=list(adv.POLICIES), prng=random.Random(r), cnt=cnt)
        chk, info, bad = adv.run(I, adv.base_opts(pfar=rng.choice([0, 0.5, 1])), random.Random(r), ch, cnt, geo=GEO)
        if any(k.startswith(cls) for k in bad):
            return ('policy', r, dict(chk.flags))
    return None


def variants(I):
    B = T.Builder(I['n'], [tuple(e) for e in I['ends']], I['rot'])
    m = len(B.ends)
    out = []
    for e in range(m):
        B2, keep = B.remove_edges({e})
        if B2.connected():
            out.append(dict(I, n=B2.n, ends=list(B2.ends), rot=B2.rot, cap=[I['cap'][k] for k in keep]))
    for e in range(m):
        u, v = B.ends[e]
        if u == v:
            continue
        r = B.contract(e)
        if r is None:
            continue
        B2, keep, ren = r
        s = ren[u] if I['s'] == v else ren.get(I['s'])
        t = ren[u] if I['t'] == v else ren.get(I['t'])
        if s is None or t is None or s == t or not B2.connected():
            continue
        out.append(dict(I, n=B2.n, ends=list(B2.ends), rot=B2.rot, cap=[I['cap'][k] for k in keep], s=s, t=t))
    for e in range(m):
        for c in {0, 1, I['cap'][e] // 2}:
            if c != I['cap'][e]:
                cap = list(I['cap'])
                cap[e] = c
                out.append(dict(I, cap=cap))
    return out


def main():
    src = json.load(open(sys.argv[1]))
    I = src.get('I', src)
    cls = tuple(sys.argv[3].split(',')) if len(sys.argv) > 3 else ('iv_', 'O', 'G_', 'c24', 'sep', 'hull', 'len_lt')
    maxruns = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    I = dict(n=I['n'], ends=[tuple(e) for e in I['ends']], rot=I['rot'], cap=I['cap'], s=I['s'], t=I['t'])
    w = failing(I, cls, maxruns)
    assert w, 'input does not fail'
    improved = True
    while improved:
        improved = False
        for J in variants(I):
            try:
                T.Emb(T.Builder(J['n'], J['ends'], J['rot']), J['cap'])
            except AssertionError:
                continue
            w2 = failing(J, cls, maxruns)
            if w2:
                I, w = J, w2
                improved = True
                print('->', I['n'], len(I['ends']), sum(I['cap']), w[0], flush=True)
                break
    res = dict(I=I, witness=w, mincut_nx=T.mincut_nx(T.inst_emb(I), I['s'], I['t']), m=len(I['ends']))
    json.dump(res, open(sys.argv[2], 'w'), indent=1, default=str)
    print(json.dumps(res, default=str)[:2000])


if __name__ == '__main__':
    main()
