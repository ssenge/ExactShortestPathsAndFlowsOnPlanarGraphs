"""Summarise the logs of testSO: runs, incisions, failures and stress coverage per method.
Usage: python3 -I aggregate.py [logs dir]"""
import sys
import os
import json
import glob
import collections

D = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs')
KEYS = ['inc', 'both_bounds', 'both_bounds_and_overlap', 'overlap_both', 'overlap_one', 'x_eq_y',
        'Q_linear_nodes>=1', 'Q_linear_nodes>=3', 'lin_split3', 'lin_unchanged', 'old_end_x', 'old_end_y',
        'old_end_both', 'Q_all_old', 'Q_old_edges>=3', 'U_or_V_crosses', 'i12_outside',
        't_strict_between_xy_in_range', 'junction_child_end_at_x_or_y', 'level>=4', 'level>=6',
        'child', 'child_both_bounds', 'child_single_index', 'ties_P', 'ties_Pi', 'changed_P', 'changed_Pi',
        'G_inc', 'G_ok_two_sides', 'G_P_checked', 'G_end_new', 'G_end_old', 'G_bound_checked',
        'G_newedge_checked', 'G_child_checked', 'K_runs', 'K_ann_checked', 'K_piece_checked', 'K_gamma_checked',
        'K_chords']
OK = ['O_INV_checked', 'O_c23_chk_core', 'O_c23_chk_below_j', 'O_node_iv_split3', 'O2_overlap_side_split',
      'O2_called_side', 'O_both_bounds', 'R_full_z', 'R_full_chk', 'R_full_neq', 'R_full_z_fail_need',
      'R_full_loses_side_min', 'R_full_only_overlap']


def group(b, r):
    if b.startswith('ends'):
        k = b.split('_')
        return 'alternative ENDS=%s of RECURSION.md: %s' % (k[0][4:], {'hits': 'saved hits', 'exh': 'exhaustive m=%s' % r.get('M'), 'hill': 'hill-climbing'}[k[1].split('.')[0]])
    if b.startswith('exhnl'):
        return 'exhaustive m=%s' % r['M']
    if b.startswith('exhstruct'):
        return 'exhaustive structured (20 s,t each)'
    if b.startswith('exhK'):
        return 'exhaustive+geo+K m=%s' % r['M']
    if b.startswith('exhgeo'):
        return 'exhaustive+geo m=%s' % r['M']
    if b.startswith('advF'):
        return 'policy, whole-path reading (F)'
    if b.startswith('advL'):
        return 'policy, long strips (depth 7+)'
    if b.startswith('hits'):
        return 'saved hits of the unrepaired recursion (testR), all runs'
    if b.startswith('adv'):
        return 'policy lanes'
    if b.startswith("hillF"):
        return "hill-climbing, whole-path reading (F)"
    if b.startswith("hill"):
        return 'hill-climbing'
    if b.startswith('s1_'):
        return 'S1/S_1 direct in A_1'
    return b


groups = collections.OrderedDict()
for f in sorted(glob.glob(os.path.join(D, '*.json'))):
    b = os.path.basename(f)
    if b.startswith(('maps', 'smoke', 'struct.json')):
        continue
    try:
        r = json.load(open(f))
    except Exception:
        continue
    G = groups.setdefault(group(b, r), collections.Counter())
    G['files'] += 1
    c = r.get('counts', {})
    for k, v in c.items():
        if isinstance(v, (int, float)) and k != 'levels_max':
            G[k] += v
    G['levels_max'] = max(G['levels_max'], c.get('levels_max', 0))
    G['nfail'] += r.get('nfail', 0)
    G['instances'] += r.get('instances', r.get('done', 0))
    G['incomplete'] += r.get('incomplete', 0)
    G['steps'] += r.get('steps', 0)
    G['secs'] += r.get('secs', 0)
    for k, v in r.get('ostats', {}).items():
        G['o:' + k] += v
for g, G in groups.items():
    print('==', g)
    print('  files %d instances %d runs %d secs %d nfail %d incomplete %d levels_max %d steps %d' % (
        G['files'], G['instances'], G['runs'], G['secs'], G['nfail'], G['incomplete'], G['levels_max'], G['steps']))
    if g.startswith('S1'):
        print('  ', {k: v for k, v in G.items() if k not in ('files', 'secs', 'nfail')})
        continue
    print('  ', {k: G[k] for k in KEYS if G[k]})
    o = {k: G['o:' + k] for k in OK if G['o:' + k]}
    if o:
        print('   driver stats:', o)
    print('   flags:', {k[5:]: v for k, v in G.items() if k.startswith('flag_')})
