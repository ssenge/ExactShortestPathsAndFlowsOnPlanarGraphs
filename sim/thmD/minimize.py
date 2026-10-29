#!/usr/bin/env python3
"""Greedy minimizer for literal-G^ counterexamples.  usage: minimize.py SEED KIND [size grid pcommon pfar]
KIND: D1 (endpoint-case edge later incised -> merged node-parts) or D2 (e0 = e_last = st edge)."""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'thmD.py')).read().replace("if __name__ == '__main__':\n    main()", "")
exec(_src)

seeds = [int(x) for x in sys.argv[1].split(',')]
KIND = sys.argv[2]
CLEAN = os.environ.get('CLEAN') == '1'
SIZE_MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 70
GRID_MAX = int(sys.argv[4]) if len(sys.argv) > 4 else 12
PC = float(sys.argv[5]) if len(sys.argv) > 5 else 0.15
PF = float(sys.argv[6]) if len(sys.argv) > 6 else 0.7
RUNS = int(os.environ.get('RUNS', '40'))
OPT_L = dict(mode='claimed', variant='literal', tiebreak='minid', pairs=0, pcommon=PC, pfar=PF)
OPT_F = dict(mode='claimed', variant='fixed', tiebreak='minid', pairs=0, pcommon=PC, pfar=PF)


def bad_run(I, rs):
    chk, info = run_one(I, OPT_L, rs)
    if KIND == 'D2':
        if not ('i_dist' in chk.flags or 'iv_value' in chk.flags):
            return None
    elif 'iv_value' not in chk.flags:
        return None
    if KIND == 'D1' and not ('struct_merge' in chk.flags and not info.get('e0_same')):
        return None
    if KIND == 'D2' and not info.get('e0_same'):
        return None
    if CLEAN:
        if 'dev_mirrored_endpoint' in chk.flags or min(I['cap']) < 1:
            return None
        if len({tuple(sorted(e)) for e in I['ends']}) != len(I['ends']):
            return None
    chk2, info2 = run_one(I, OPT_F, rs)
    if any(not k.startswith(('dev_', 'xa_', 'xb_')) for k in chk2.flags):
        return None   # want the fixed variant clean on the same choices
    return (chk, info)


def pred(I):
    for rs in range(RUNS):
        r = bad_run(I, rs)
        if r:
            return rs
    return None


def from_builder(B, cap, s, t):
    return dict(n=B.n, ends=list(B.ends), rot=[list(r) for r in B.rot], cap=list(cap), s=s, t=t)


def candidates(I):
    B = Builder(I['n'], I['ends'], I['rot'])
    s, t = I['s'], I['t']
    out = []
    for x in range(B.n):
        if x in (s, t):
            continue
        B2, keep, ren = B.delete_vertex(x)
        if B2.n >= 2 and B2.connected():
            out.append(from_builder(B2, [I['cap'][e] for e in keep], ren[s], ren[t]))
    for e in range(len(B.ends)):
        B2, keep = B.remove_edges({e})
        if B2.connected():
            out.append(from_builder(B2, [I['cap'][k] for k in keep], s, t))
    for e in range(len(B.ends)):
        u, v = B.ends[e]
        if {u, v} == {s, t}:
            continue
        r = B.contract(e)
        if r is None:
            continue
        B2, keep, ren = r
        s2 = ren[u] if s == v else ren[s]
        t2 = ren[u] if t == v else ren[t]
        if s2 != t2 and B2.connected() and B2.euler_ok():
            out.append(from_builder(B2, [I['cap'][k] for k in keep], s2, t2))
    for e in range(len(B.ends)):
        for c in (0, 1, I['cap'][e] // 2):
            if c < I['cap'][e]:
                J = dict(I)
                J['cap'] = list(I['cap'])
                J['cap'][e] = c
                out.append(J)
    return out


def size(I):
    return (I['n'] + len(I['ends']), sum(min(c, 10) for c in I['cap']))


rs = None
for seed in seeds:
    I0 = make_instance(seed)
    I = from_builder(Builder(I0['n'], I0['ends'], I0['rot']), I0['cap'], I0['s'], I0['t'])
    rs = pred(I)
    if rs is not None:
        break
assert rs is not None, "no seed reproduces"
improved = True
while improved:
    improved = False
    cs = sorted(candidates(I), key=size)
    for J in cs:
        if size(J) >= size(I):
            continue
        try:
            r = pred(J)
        except Exception:
            r = None
        if r is not None:
            I = J
            rs = r
            improved = True
            print('  ->', size(I), file=sys.stderr)
            break

chk, info = run_one(I, OPT_L, rs)
chk2, info2 = run_one(I, OPT_F, rs)
emb = inst_emb(I)
res = dict(kind=KIND, seed=seed, run_seed=rs, n=I['n'], ends=I['ends'], cap=I['cap'], rot=I['rot'], s=I['s'], t=I['t'],
           faces=[[(emb.tl[d], emb.head(d)) for d in cyc] for cyc in emb.faces],
           mincut=info.get('mincut'), reported_literal=info.get('reported'), reported_fixed=info2.get('reported'),
           P_faces=info.get('pf'), P_edges=info.get('Pedges'), eps=info.get('eps'), ept=info.get('ept'),
           incised=info.get('incised_per_level'), literal_flags=dict(chk.flags), fixed_flags=dict(chk2.flags),
           notes=[str(x) for x in chk.notes[:12]])
print(json.dumps(res, default=str))
