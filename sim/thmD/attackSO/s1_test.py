"""Direct tests of Lemma S1 and (S_1) in A_1 (RECURSION.md), independent of the recursion.

For an instance and every (f, g, w-shortest P (up to maxP), legal corner at s, at t):
  build A_1 (the driver's level1_ann), lambda_t with w = K c + 1 (K = 10^9);
  for every i and EVERY w-shortest path Pbar from p_i^0 to p_i^1 (up to a cap):
    S1b  i1 = min(i, x, y), i2 = max(i, x, y);
    S1a  w(U) = d(i, x), w(V) = d(y, i);
    S1   for t in (i1, i2): lambda_q <= lambda_t on [i1, t] or on [t, i2];
    S_1  for t strictly between x and y: p_t^0, p_t^1 disconnected in A_1 minus the nodes of Qbar;
  (S_1) in general: for every x, y with |x - y| >= 2 and EVERY simple path Qbar from p_x^0 to
    p_y^1 whose internal nodes are off P (up to a cap), and every t strictly between: Qbar separates.
Usage: python3 -I s1_test.py maps MAPS.json M SHARD NSH OUT [maxsec]
       python3 -I s1_test.py rand START COUNT OUT [maxsec]
"""
import sys
import os
import json
import time
import random
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv

T = adv.T
KB = adv.KB


def corner_options(emb, v, face, Pedges):
    dv = emb.deg(v)
    return [i for i in range(dv) if emb.corner_face(v, i) == face and
            ((emb.rot[v][i] >> 1) not in Pedges or (emb.rot[v][(i + 1) % dv] >> 1) not in Pedges)]


def a1_instances(emb, s, t, rng, maxP=6):
    sfaces = sorted({emb.corner_face(s, i) for i in range(emb.deg(s))})
    tfaces = sorted({emb.corner_face(t, i) for i in range(emb.deg(t))})
    for f in sfaces:
        for g in tfaces:
            ctx0 = T.Ctx(emb)
            A0 = T.level0_ann(ctx0)
            face2np = {X.face: X.id for X in A0.nodes.values()}
            Ps, _ = adv.SPDag(A0, emb, face2np[f], face2np[g]).paths(maxP, rng)
            for Pn, Pe in Ps:
                pf = [ctx0.store[x].face for x in Pn]
                m = len(pf) - 1
                Pedges = set()
                pdart = {}
                for k, (la, lb) in enumerate(Pe):
                    Pedges.add(la[0] >> 1)
                    pdart[k + 1] = {pf[k]: la[0], pf[k + 1]: lb[0]}
                for cs in corner_options(emb, s, pf[0], Pedges):
                    for ct in corner_options(emb, t, pf[m], Pedges):
                        ctx = T.Ctx(emb)
                        try:
                            A1 = T.level1_ann(ctx, pf, pdart, (s, cs), (t, ct))
                        except AssertionError:
                            yield None
                            continue
                        yield (pf, A1, ctx, f, g, cs, ct)


def connected_without(adj, a, b, removed):
    if a in removed or b in removed:
        return False
    seen = {a}
    st = [a]
    while st:
        x = st.pop()
        if x == b:
            return True
        for y, _, _, _ in adj[x]:
            if y not in seen and y not in removed:
                seen.add(y)
                st.append(y)
    return False


def test_A1(emb, A1, ctx, cnt, fails, tag, capPi=200, capQ=300, generalQ=True, mincut=None):
    m = max(t for (t, b) in A1.piece)
    adj = adv.ann_adj(A1, emb)
    lam = {t: adv.dijk(adj, A1.piece[(t, 0)])[A1.piece[(t, 1)]] for t in range(m + 1)}
    if mincut is not None and min(lam.values()) // KB != mincut:
        fails.append((tag, 'reif_reduction', min(lam.values()) // KB, mincut))
    d0 = {u: adv.dijk(adj, A1.piece[(u, 0)]) for u in range(m + 1)}

    def dP(u, v):
        return d0[u][A1.piece[(v, 0)]]
    anc = {x: ctx.store[x].anc for x in A1.nodes}
    rng = random.Random(1)
    for i in range(m + 1):
        ps, trunc = adv.SPDag(A1, emb, A1.piece[(i, 0)], A1.piece[(i, 1)]).paths(capPi, rng)
        cnt['Pbar'] += len(ps)
        cnt['Pbar_trunc'] += trunc
        for nodes, edges in ps:
            a = [anc[x] for x in nodes]
            last0 = max(k for k, z in enumerate(a) if z[0] == 'p' and z[2] == 0)
            first1 = min(k for k, z in enumerate(a) if k > last0 and z[0] == 'p' and z[2] == 1)
            x, y = a[last0][1], a[first1][1]
            tid = [z[1] for z in a if z[0] == 'p']
            i1, i2 = min(tid), max(tid)
            if (i1, i2) != (min(i, x, y), max(i, x, y)):
                fails.append((tag, 'S1b', i, x, y, i1, i2))
            wU = sum(KB * emb.cap[la[0] >> 1] + 1 for la, lb in edges[:last0])
            wV = sum(KB * emb.cap[la[0] >> 1] + 1 for la, lb in edges[first1:])
            if wU != dP(i, x) or wV != dP(y, i):
                fails.append((tag, 'S1a', i, x, y))
            if any(z[0] == 'p' and z[2] == 1 for z in a[:last0]):
                cnt['U_has_1copy'] += 1
            for t in range(i1 + 1, i2):
                cnt['S1_checks'] += 1
                if min(x, y) < t < max(x, y):
                    cnt['S1_case2'] += 1
                if not (all(lam[q] <= lam[t] for q in range(i1, t + 1)) or
                        all(lam[q] <= lam[t] for q in range(t, i2 + 1))):
                    fails.append((tag, 'S1_interval', i, t, i1, i2, x, y))
            Qset = set(nodes[last0:first1 + 1])
            for t in range(min(x, y) + 1, max(x, y)):
                cnt['Ssep_checks'] += 1
                if connected_without(adj, A1.piece[(t, 0)], A1.piece[(t, 1)], Qset):
                    fails.append((tag, 'S_1_shortestQ', i, t, x, y))
    if not generalQ:
        return
    offP = {x for x in A1.nodes if anc[x][0] != 'p'}
    for x in range(m + 1):
        for y in range(m + 1):
            if abs(x - y) < 2:
                continue
            src, tgt = A1.piece[(x, 0)], A1.piece[(y, 1)]
            nQ = [0]

            def rec(v, onpath):
                if nQ[0] >= capQ:
                    return
                for w_, _, _, _ in adj[v]:
                    if w_ == tgt:
                        nQ[0] += 1
                        Qs = onpath | {tgt}
                        for t in range(min(x, y) + 1, max(x, y)):
                            cnt['Sgen_checks'] += 1
                            if connected_without(adj, A1.piece[(t, 0)], A1.piece[(t, 1)], Qs):
                                fails.append((tag, 'S_1_general', x, y, t, sorted(Qs)))
                        continue
                    if w_ in offP and w_ not in onpath:
                        onpath.add(w_)
                        rec(w_, onpath)
                        onpath.discard(w_)
            rec(src, {src})
            cnt['Sgen_Q'] += nQ[0]
            cnt['Sgen_Q_trunc'] += nQ[0] >= capQ


def run_inst(I, cnt, fails, rng, maxP=6, generalQ=True, capQ=300):
    emb = T.inst_emb(I)
    mc = T.mincut_nx(emb, I['s'], I['t'])
    for item in a1_instances(emb, I['s'], I['t'], rng, maxP):
        if item is None:
            cnt['a1_assert'] += 1
            continue
        pf, A1, ctx, f, g, cs, ct = item
        cnt['A1'] += 1
        test_A1(emb, A1, ctx, cnt, fails, (I.get('seed'), f, g, tuple(pf), cs, ct), generalQ=generalQ,
                capQ=capQ, mincut=mc)


if __name__ == '__main__':
    mode = sys.argv[1]
    cnt = collections.Counter()
    fails = []
    t0 = time.time()
    rng = random.Random(5)
    if mode == 'maps':
        mapsf, M, shard, nsh, out = sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        maxsec = float(sys.argv[7]) if len(sys.argv) > 7 else 3300
        for mi, (n, ends, rot) in enumerate(json.load(open(mapsf))[M]):
            if mi % nsh != shard:
                continue
            if time.time() - t0 > maxsec:
                cnt['stopped_early'] = 1
                break
            cnt['maps'] += 1
            for cname, cap in (('one', [1] * len(ends)), ('r', [random.Random(mi).randint(0, 2) for _ in ends])):
                for s in range(n):
                    for t in range(n):
                        if s != t:
                            I = dict(seed=(mi, cname, s, t), n=n, ends=ends, rot=rot, cap=cap, s=s, t=t)
                            run_inst(I, cnt, fails, rng, maxP=4, capQ=200)
    else:
        start, count, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        maxsec = float(sys.argv[5]) if len(sys.argv) > 5 else 3300
        import gens
        for sd in range(start, start + count):
            if time.time() - t0 > maxsec:
                cnt['stopped_early'] = 1
                break
            I = gens.make(sd)
            if I['n'] > 45:
                continue
            cnt['inst'] += 1
            run_inst(I, cnt, fails, rng, maxP=2, generalQ=(I['n'] <= 20), capQ=100)
    json.dump(dict(argv=sys.argv, counts=dict(cnt), nfail=len(fails), fails=[str(f)[:500] for f in fails[:50]],
                   secs=round(time.time() - t0, 1)), open(out, 'w'), indent=1)
    print(json.dumps(dict(counts=dict(cnt), nfail=len(fails), secs=round(time.time() - t0, 1))))
