"""Greedy minimization of an e2e counterexample (simulated [18, Alg. 3] misses lambda with all
shortest paths unique). Deletes edges, contracts edges (keeping G simple), then scales the
capacities down. A step is kept if some (f, g, legal corners) still fails with unique paths.
usage: python3 -I minimize_e2e.py HITS.json INDEX OUT.json"""
import sys, os, json, random, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emb import Emb
from deep import Run


def mk(I):
    return Emb(I['n'], [tuple(e) for e in I['ends']], I['rot'], I['cap'])


def connected(n, ends):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for u, v in ends:
        par[f(u)] = f(v)
    return len({f(x) for x in range(n)}) == 1


def simple(ends):
    return len({frozenset(e) for e in ends}) == len(ends) and all(u != v for u, v in ends)


def one(I, fg, cuts):
    emb = mk(I)
    C = collections.Counter()
    notes = []
    R = Run(emb, I['s'], I['t'], random.Random(1), 'random', frozenset(), C, notes, {})
    R.force_fg = fg
    R.force_cuts = cuts
    R.run()
    other = sorted(k for k in C if k.startswith('BAD_') and not k.startswith('BAD_e2e'))
    got = min((r[2] for r in R.results), default=None)
    return dict(fail=C['BAD_e2e_value'] > 0, unique=R.nonunique == 0, got=got, lam=R.lam, other=other,
                legal=R.legal, pf=R.pf, pe=R.pe)


def witnesses(I, first_only=True):
    emb = mk(I)
    s, t = I['s'], I['t']
    sf = sorted({emb.corner_face((s, i)) for i in range(emb.deg(s))})
    tf = sorted({emb.corner_face((t, i)) for i in range(emb.deg(t))})
    out = []
    tot = 0
    for f in sf:
        for g in tf:
            try:
                r0 = one(I, (f, g), None)
            except Exception:
                continue
            ls, lt = r0['legal']
            for cs in ls:
                for ct in lt:
                    try:
                        r = one(I, (f, g), (cs, ct))
                    except Exception:
                        continue
                    tot += 1
                    if r['fail'] and r['unique']:
                        out.append(dict(fg=(f, g), cuts=(cs, ct), got=r['got'], lam=r['lam'], other=r['other'],
                                        pf=r['pf'], pe=r['pe']))
                        if first_only:
                            return out, tot
    return out, tot


def delete_edge(I, e):
    ends = [x for k, x in enumerate(I['ends']) if k != e]
    if not connected(I['n'], ends):
        return None
    newid = {k: (k if k < e else k - 1) for k in range(len(I['ends'])) if k != e}
    rot = [[2 * newid[d >> 1] + (d & 1) for d in r if (d >> 1) != e] for r in I['rot']]
    if any(len(r) == 0 for r in rot):
        return None
    cap = [c for k, c in enumerate(I['cap']) if k != e]
    return dict(I, ends=ends, rot=rot, cap=cap)


def contract_edge(I, e):
    u, v = I['ends'][e]
    if {u, v} == {I['s'], I['t']}:
        return None
    if v in (I['s'], I['t']):
        u, v = v, u
        # contract into the terminal
    ru, rv = I['rot'][u], I['rot'][v]
    du = 2 * e if I['ends'][e][0] == u else 2 * e + 1
    dv = du ^ 1
    iu, iv = ru.index(du), rv.index(dv)
    new_ru = ru[iu + 1:] + ru[:iu] + rv[iv + 1:] + rv[:iv]
    rot = [list(r) for r in I['rot']]
    rot[u] = new_ru
    rot[v] = []
    ends = [((u if a == v else a), (u if b == v else b)) for (a, b) in I['ends']]
    ends[e] = (u, u)
    if not simple([x for k, x in enumerate(ends) if k != e]):
        return None
    keep = [k for k in range(len(ends)) if k != e]
    newid = {k: i for i, k in enumerate(keep)}
    rot2 = [[2 * newid[d >> 1] + (d & 1) for d in r if (d >> 1) != e] for r in rot]
    ren = {w: (w if w < v else w - 1) for w in range(I['n']) if w != v}
    ends2 = [(ren[a], ren[b]) for k, (a, b) in enumerate(ends) if k != e]
    rot3 = [rot2[w] for w in range(I['n']) if w != v]
    cap = [I['cap'][k] for k in keep]
    return dict(I, n=I['n'] - 1, ends=ends2, rot=rot3, cap=cap, s=ren[I['s']], t=ren[I['t']])


def ok(I):
    E = mk(I)
    if not E.genus_ok():
        return False
    w, _ = witnesses(I)
    return bool(w)


def main():
    hits = json.load(open(sys.argv[1]))['hits']
    h = hits[int(sys.argv[2])]
    I = dict(n=h['n'], ends=[tuple(e) for e in h['ends']], rot=h['rot'], cap=h['cap'], s=h['s'], t=h['t'])
    assert ok(I), 'start instance does not fail'
    changed = True
    while changed:
        changed = False
        for e in range(len(I['ends'])):
            J = delete_edge(I, e)
            if J is not None and ok(J):
                I = J
                changed = True
                print('deleted edge; m =', len(I['ends']), file=sys.stderr)
                break
        if changed:
            continue
        for e in range(len(I['ends'])):
            J = contract_edge(I, e)
            if J is not None and ok(J):
                I = J
                changed = True
                print('contracted edge; n =', I['n'], file=sys.stderr)
                break
    for D in (300000, 100000, 30000, 10000, 3000, 1000, 300, 100, 30, 10):
        J = dict(I, cap=[max(1, round(c / D)) for c in I['cap']])
        if ok(J):
            I = J
            print('scaled caps by', D, file=sys.stderr)
            break
    # per-edge: try smaller caps
    changed = True
    while changed:
        changed = False
        for e in range(len(I['ends'])):
            for c in [x for x in (1, 2, 3, 5, 8, 13, 20, 30, 50) if x < I['cap'][e]]:
                cap = list(I['cap'])
                cap[e] = c
                J = dict(I, cap=cap)
                if ok(J):
                    I = J
                    changed = True
                    break
            if changed:
                break
    allw, tot = witnesses(I, first_only=False)
    json.dump(dict(instance=I, witnesses=allw, choices_tried=tot), open(sys.argv[3], 'w'), default=str)
    print(json.dumps(dict(n=I['n'], m=len(I['ends']), s=I['s'], t=I['t'], cap=I['cap'],
                          failing_choices=len(allw), choices=tot)))


if __name__ == '__main__':
    main()
