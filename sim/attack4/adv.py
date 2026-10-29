"""adv9 driver: python3 -I adv.py CONF START:END fam1,fam2,... [scale] [light]
Runs engine_r9 (copy of sim/s9/engine_r.py + exact holes, B2/B3/B4/Claim7_R violation recording,
through-hole virtual closings, greedy adversarial separator modes) on old and new families."""
import sys, os, random, collections, time, json
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(REPO, 's9'))
sys.path.insert(0, os.path.join(REPO, 'attack3'))
sys.path.insert(0, HERE)
import networkx as nx, numpy as np
from sweep import params as params_old, MODES_ALL
from geo import FAMS, virtual_candidates, drawing_ok
from core import PG, Fail, seg_cross
if os.environ.get('ENGINE') == 'c':
    from engine_c9 import EngineC as Engine
else:
    from engine_r9 import Engine
from fams9 import FAMS9, params9

F0 = dict(zall=0.0, txmode='bfs', degenerate=False)
CONF = {
    'faithful': dict(F0, modes={"bal": 3, "bnd": 1, "virt": 1, "onG": 1, "rand": 1}, swap=0.0, tries=120),
    'strict': dict(F0, modes={"bal": 3, "bnd": 1, "virt": 1, "onG": 1, "rand": 1}, swap=0.0, tries=200, strict=True),
    'advb0': dict(F0, modes=MODES_ALL, swap=0.5, tries=120),
    'pxb': dict(F0, modes={"avoid": 6, "bal": 1}, swap=0.3, tries=400, bal=0.97),
    'chb': dict(F0, modes={"chord": 4, "bnd": 1, "bal": 1}, swap=0.3, tries=200),
    # through-hole closings
    'vh': dict(F0, modes={"vhole": 5, "bal": 1, "bnd": 1, "rand": 1}, swap=0.3, tries=150, vhole=0.6, bal=0.95),
    'vhs': dict(F0, modes={"vhole": 8, "bal": 1}, swap=0.0, tries=200, vhole=1.0, bal=0.97),
    # greedy adversaries (all may use through-hole closings)
    'gB2': dict(F0, modes={"advB2": 6, "advC": 2, "bal": 1}, swap=0.3, tries=150, vhole=0.5, adv_k=24, bal=0.95),
    'gB3': dict(F0, modes={"advB3": 6, "advH": 2, "advA": 2, "bal": 1}, swap=0.3, tries=150, vhole=0.6, adv_k=24, bal=0.95),
    'gB4': dict(F0, modes={"advB4": 6, "advH": 3, "bal": 1}, swap=0.3, tries=150, vhole=0.6, adv_k=24, bal=0.95),
    'gH': dict(F0, modes={"advH": 8, "bal": 1}, swap=0.3, tries=150, vhole=0.6, adv_k=24, bal=0.95, advbal=0.99),
    'gC': dict(F0, modes={"advC": 8, "bal": 1}, swap=0.3, tries=150, vhole=0.4, adv_k=24, bal=0.95, advbal=0.99),
    'gM': dict(F0, modes={"advM": 6, "advH": 2, "advC": 2, "vhole": 1}, swap=0.4, tries=150, vhole=0.6, adv_k=24, bal=0.95, advbal=0.99),
}
for obj in ('advM', 'advB2', 'advB3', 'advB4'):
    CONF['x' + obj[3:]] = dict(F0, modes={obj: 1}, swap=0.4, tries=300, vhole=1.0, adv_k=300, bal=0.999, advbal=0.999,
                                vhole_cap=600)
CONF['cb'] = dict(F0, modes={"comb": 5, "bal": 1, "rand": 1}, swap=0.3, tries=150, comb=0.7, comb_cap=300, bal=0.95, combcheck=True)
CONF['cbx'] = dict(F0, modes={"advM": 4, "advB3": 2, "advB4": 2, "advH": 1, "comb": 1}, swap=0.4, tries=200, comb=1.0,
                   comb_cap=300, adv_k=40, bal=0.97, advbal=0.99)
for k in list(CONF):
    if not k.startswith('hi_'):
        CONF[k + '_dfsT'] = dict(CONF[k], Tglob='dfs')
        CONF[k + '_rndT'] = dict(CONF[k], Tglob='rand')
for m in ('avoid', 'chord', 'bnd', 'virt', 'onG', 'rand', 'long'):
    CONF['hi_' + m] = dict(F0, modes={m: 12, "bal": 1}, swap=0.3, tries=200, vhole=0.3, bal=0.97)

KEYS_MX = ('mult_region', 'Tcomp', 'Tcomp_minus_depth', 'L_per_vertex_max', 'L_blocks_max', 'aY_max', 'aY_minus_holesX',
           'aY_minus_hXex', 'holesX_minus_depth', 'hEx_max', 'hEx_minus_depth', 'hY_minus_hX', 'B2_slack',
           'cX_minus_depth1', 'c_minus_h1', 'hX_engine_under_by', 'depth_max', 'outkids_per_s', 'inside_parts_max', 'lp47_comp_growth')


def metrics(eng):
    g = eng.g; mx = collections.defaultdict(float); st = collections.Counter()
    byd = collections.defaultdict(list)
    for b, B in eng.bags.items():
        byd[B['depth']].append(b)
    for d, bs in byd.items():
        mr = collections.Counter(); sides = collections.Counter()
        for b in bs:
            B = eng.bags[b]
            for e, sd in B['E'].items():
                mr[e] += 1
                for t in sd:
                    sides[(e, t)] += 1
            cT = eng.comps_T(B['X'], B['E'])
            mx['Tcomp'] = max(mx['Tcomp'], cT); mx['Tcomp_minus_depth'] = max(mx['Tcomp_minus_depth'], cT - (d + 1))
            hB = eng.holes_euler(B['E'])
            mx['c_minus_h1'] = max(mx.get('c_minus_h1', -99), cT - hB - 1)
            st['bags'] += 1
            if d >= 8:
                st['bags_d8'] += 1
            if d >= 12:
                st['bags_d12'] += 1
        if mr:
            mx['mult_region'] = max(mx['mult_region'], max(mr.values()))
            if max(mr.values()) > 2:
                eng.viol('B1a: edge in > 2 region graphs at one depth', (d, max(mr.values())))
            if max(sides.values()) > 1:
                eng.viol('B1a: side in two bags of one depth', d)
        mx['depth_max'] = max(mx['depth_max'], d)
    return st, mx


def build(fam, s, r, scale):
    if fam in FAMS9:
        args = params9(fam, r, scale)
        pos, E = FAMS9[fam](s, args)
    else:
        args = params_old(fam, r)
        if scale > 1:
            for k_ in ('n', 'k', 'm', 'K', 'extra'):
                if k_ in args and not isinstance(args[k_], bool):
                    args[k_] = int(args[k_] * (scale if k_ in ('n', 'm', 'extra') else scale ** 0.5))
            if 'R' in args:
                args['R'] = int(args['R'] * scale ** 0.5)
        pos, E = FAMS[fam](s, args)
    return args, pos, E


if __name__ == '__main__':
    conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':'))
    fams = sys.argv[3].split(',')
    scale = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
    light = not (len(sys.argv) > 5 and sys.argv[5] == 'full')
    leafs = [int(x) for x in os.environ.get('LEAFS', '6,8,10').split(',')]
    tot = collections.defaultdict(collections.Counter); mx = collections.defaultdict(lambda: collections.defaultdict(float))
    viols = []; t0 = time.time(); nfail = 0
    for s in range(a, b):
        r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]
        try:
            args, pos, E = build(fam, s, r, scale)
        except Exception as ex:
            tot[fam]['build_error'] += 1; continue
        if len(pos) < 12 or not drawing_ok(pos, E):
            tot[fam]['bad_instance'] += 1; continue
        try:
            g = PG(pos, E, seed=s)
        except AssertionError:
            tot[fam]['bad_instance'] += 1; continue
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice(leafs); cfg['light'] = light
        vc0 = virtual_candidates(pos, E); P_ = np.asarray(pos, float)
        A_ = P_[[x for x, y in E]]; B_ = P_[[y for x, y in E]]
        vc = {pr for pr in vc0 if not seg_cross(P_[pr[0]], P_[pr[1]], A_, B_, eps=0.0)}
        tot[fam]['vc_dropped_crossing'] += len(vc0) - len(vc)
        eng = Engine(g, vc, random.Random(s * 7919 + 1), cfg)
        try:
            eng.run()
        except Fail as ex:
            tot[fam]['FAILED'] += 1; nfail += 1
            print('FAIL', conf, fam, s, args, ex.args, flush=True)
        st, m = metrics(eng)
        tot[fam].update(eng.st); tot[fam].update(st); tot[fam]['instances'] += 1; tot[fam]['n_total'] += g.n
        for k, v in list(eng.mx.items()) + list(m.items()):
            mx[fam][k] = max(mx[fam][k], v)
        if eng.ce:
            viols.append((fam, s, args, eng.ce[:5]))
            print('VIOL', conf, fam, s, json.dumps(args), eng.ce[:5], flush=True)
    keys = ('instances', 'n_total', 'FAILED', 'bags', 'bags_d8', 'bags_d12', 'separators', 'virtual_closings',
            'vhole_bags', 'vhole_used', 'B2_checks', 'B4_checks', 'aY_checks', 'aY_gt_max1_holes', 'aY_gt_max1_hex_VIRT',
            'aY_gt_max1_hex_VHOLE', 'aY_gt_bound', 'aY_gt_max1_holes_REALCLOSING', 'hX_engine_under', 'hX_engine_over',
            'claim7_vertex_checks', 'R_side_lost', 'rule3_no_holder', 'separator_encloses_foreign_vertex', 'tiles_checked',
            'z_inherited_in_inside_wedge', 'bad_instance', 'build_error', 'comb_bags', 'comb_cands', 'comb_used',
            'combcheck_ok', 'closing_crosses_nonregion_edge', 'vc_dropped_crossing')
    for fam in tot:
        print('FAM', conf, fam, {k: tot[fam][k] for k in keys if tot[fam][k]},
              {k: v for k, v in tot[fam].items() if k.startswith('VIOL') or k.startswith('FAIL')})
        print('   MX', {k: round(mx[fam][k], 2) for k in KEYS_MX if k in mx[fam]})
    T = collections.Counter()
    for fam in tot:
        T.update(tot[fam])
    G = collections.defaultdict(float)
    for fam in mx:
        for k, v in mx[fam].items():
            G[k] = max(G[k], v)
    print('TOTAL', conf, {k: T[k] for k in keys if T[k]}, {k: v for k, v in T.items() if k.startswith('VIOL') or k.startswith('FAIL')})
    print('TOTMX', conf, {k: round(G[k], 2) for k in KEYS_MX if k in G})
    print('NVIOL', len(viols), 'NFAIL', nfail, 'secs', round(time.time() - t0), flush=True)
