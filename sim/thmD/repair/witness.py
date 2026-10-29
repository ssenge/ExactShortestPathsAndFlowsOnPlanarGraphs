"""Named degenerate instances for Lemma R, each under many run seeds and both endpoint rules."""
import sys, json, random
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.dirname(HERE)]  # repair/ and sim/thmD/
import test_repair as T
thmD = T.thmD
B_ = thmD.Builder


def inst(B, cap, s, t):
    return dict(n=B.n, ends=list(B.ends), rot=[list(r) for r in B.rot], cap=list(cap), s=s, t=t)


W = {}
W['D1_n4'] = dict(n=4, ends=[(0, 3), (0, 1), (1, 2), (2, 3), (3, 1)], rot=[[2, 0], [4, 9, 3], [5, 6], [7, 1, 8]],
                  cap=[1, 1, 1, 1, 5], s=1, t=2)
for c in (0, 3):
    W['D2_single_edge_c%d' % c] = dict(n=2, ends=[(0, 1)], rot=[[0], [1]], cap=[c], s=1, t=0)
# n=2, three parallel edges
B = B_(2, [(0, 1)], [[0], [1]])
B.add_parallel(0); B.add_parallel(0)
W['n2_par3'] = inst(B, [0, 1, 2], 0, 1)
# n=3: pendant s on 0, three parallel 0-1 edges, t=1
B = B_(2, [(0, 1)], [[0], [1]])
B.add_parallel(0); B.add_parallel(0)
w = B.add_pendant(0, random.Random(1))
W['n3_pendant_par'] = inst(B, [0, 0, 1, 1], w, 1)
# path s-a-t
W['path3'] = inst(B_(3, [(0, 1), (1, 2)], [[0], [1, 2], [3]]), [2, 1], 0, 2)
# C4, s,t opposite (deg 2)
B = B_(4, [(0, 1), (1, 2), (2, 3), (3, 0)], [[0, 7], [1, 2], [3, 4], [5, 6]])
W['C4_opposite'] = inst(B, [1, 2, 1, 3], 0, 2)
W['C4_adjacent'] = inst(B, [1, 2, 1, 3], 0, 1)
# wheel-ish: K4
G = thmD.nx.complete_graph(4)
B = B_.from_nx(G)
W['K4'] = inst(B, [1, 2, 3, 1, 2, 3], 0, 3)
# grid 4x4 with pendants at s and t (deg-1 terminals far apart)
G = thmD.nx.grid_2d_graph(4, 4)
B = B_.from_nx(G)
rr = random.Random(5)
sp = B.add_pendant(0, rr)
tp = B.add_pendant(15, rr)
W['grid_pendant_st'] = inst(B, [1] * len(B.ends), sp, tp)
B2 = B_.from_nx(G)
W['grid_corner_st'] = inst(B2, [1] * len(B2.ends), 0, 15)
# bridge between two triangles, s and t on the two sides
G = thmD.nx.Graph([(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)])
B = B_.from_nx(G)
W['bridge'] = inst(B, [1] * len(B.ends), 0, 5)

out = {}
for name, I in W.items():
    for rule in ('formal', 'anylegal'):
        nbad = 0
        T.CNT.clear()
        del T.NOTES[:]
        for rs in range(300):
            opts = dict(mode='claimed', variant='fixed', tiebreak='random', pairs=1, pcommon=0.5, pfar=0.5, e0rule=rule)
            chk, info = T.run_one(I, opts, rs)
            bad = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
            if bad:
                nbad += 1
                T.note('THMD_FLAG', (rs, bad))
        badc = {k: v for k, v in T.CNT.items() if k.startswith(('P1_', 'P2_', 'P3_euler_fail', 'P3_rot', 'P3_dis',
                                                                  'P4_', 'P6_amb', 'P6_parent', 'FactN', 'closed',
                                                                  'DEF_mis', 'harness', 'THMD'))}
        stats = {k: v for k, v in T.CNT.items() if k.startswith(('cut_mode', 'e0_', 'terminal', 'X_deg', 'DEF_match',
                                                                   'P3_euler_ok', 'P6_X'))}
        out['%s/%s' % (name, rule)] = dict(thmD_bad=nbad, bad=badc, stats=stats, notes=[str(x)[:300] for x in T.NOTES[:3]])
print(json.dumps(out, indent=1))
