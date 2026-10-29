"""On sides with overlap: would [18]'s implemented test (Claim 5.8: discard iff a bad edge) call a
nonempty subgraph there?  Seeds of a side as in the driver: the parts of g_x, g_y on that side and
the P-pieces on that side."""
import sys, os, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD_R as T
orig = T.referee_checks
cnt = collections.Counter()
ex = []
cur = {}
def wrap(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, i1, i2, ov, true_w, KB, emb, stats, chk):
    X0, Y1 = Qn[0], Qn[-1]
    xt, yt = A.nodes[X0].anc[1], A.nodes[Y1].anc[1]
    def lowhigh(x):
        if x not in pieces:
            return None, None
        ps = pieces[x]
        Xn = A.nodes[x]
        return (ps[0], ps[1]) if Xn.lowfirst else (ps[1], ps[0])
    lx, hx = lowhigh(X0)
    ly, hy = lowhigh(Y1)
    chain = {'l': [], 'r': []}
    for z, Z in newnodes.items():
        an = Z.anc
        if an[0] != 'p' or z in (X0, Y1):
            continue
        ref = xt if an[2] == 0 else yt
        if an[1] < ref:
            chain['l'].append(z)
        elif an[1] > ref:
            chain['r'].append(z)
    seeds = {'l': [z for z in [lx, ly] if z] + chain['l'], 'r': [z for z in [hx, hy] if z] + chain['r']}
    PiE = {frozenset(e) for e in Pe_}
    bad = set()
    for ch in (A.left, A.right):
        if ch is None:
            continue
        inter = set(Pn_) & set(ch['nodes'])
        for (la, lb) in ch['edges']:
            if frozenset((la, lb)) in PiE:
                continue
            if A.ldmap[la] in inter or A.ldmap[lb] in inter:
                bad.add(la); bad.add(lb)
    for sname in ('l', 'r'):
        if not ov.get((A.aid, sname)):
            continue
        cnt['overlap_side'] += 1
        cs = {comp[z] for z in seeds[sname] if z in comp}
        if not cs:
            cnt['overlap_side_no_seed'] += 1
            continue
        free = [c for c in cs if not any(ld in bad for z in newnodes if comp[z] == c for ld in newnodes[z].seq)]
        if free:
            cnt['overlap_side_with_subgraph_without_bad_edge'] += 1
            rngok = (A.j <= i1) if sname == 'l' else (i2 <= A.k)
            if rngok:
                cnt['..._and_nonempty_range'] += 1
                if len(ex) < 5:
                    ex.append(dict(seed=cur['sd'], aid=A.aid, side=sname, j=A.j, k=A.k, i=i, i1=i1, i2=i2))
    return orig(A, i, Pn_, Pe_, Qn, Qe, newnodes, pieces, comp, i1, i2, ov, true_w, KB, emb, stats, chk)
T.referee_checks = wrap
opts = dict(mode='claimed', variant='fixed', tiebreak='random', pairs=1, pcommon=0.5, pfar=0.3,
            e0rule='formal', ends=1, lemO=1)
for sd in range(4000000, 4020000):
    cur['sd'] = sd
    I = T.make_instance(sd, None)
    chk, info = T.run_one(I, opts, sd * 1000 + 7)
print(json.dumps(dict(cnt)), ex)
