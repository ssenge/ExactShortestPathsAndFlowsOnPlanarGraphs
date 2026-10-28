"""Aggregate COUNTS/MAX lines of logs/*.log -> table (usage: python3 summarize.py [glob])."""
import sys, glob, ast, collections
pat = sys.argv[1] if len(sys.argv) > 1 else 'logs/*.log'
keys = ['instances', 'vertices', 'bags', 'nonleaf', 'max_depth', 'tiles', 'monge_checks', 'lp_checks', 'e2e_components',
        'e2e_monge_checks', 'T4b_glue_checks', 'wheel_tau_checks', 'H_wheel_checks', 'T5_order_checks', 'T5_class_checks',
        'rank_face_checks', 'claim4_checks', 'claim4b_checks', 'claim5_checks', 'claim7_vertex_checks', 'claim7_J_checks',
        'virtual_closings', 'digon_separators', 'empty_interior', 'sep_meets_anc_1(pinch)', 'q_all_outside', 'q_edges_outside',
        'bag_no_own_edges', 'P_used', 'bags_violating_7a', 'prop6_violated_instances']
tot = collections.Counter(); mx = collections.defaultdict(float); fails = 0; rows = []
for f in sorted(glob.glob(pat)):
    c = m = None; fam = None
    for line in open(f):
        if line.startswith('FAMILY'):
            fam = line.split()
            fails += int(fam[fam.index('fails') + 1])
        elif line.startswith('COUNTS'):
            c = ast.literal_eval(line[len('COUNTS '):])
        elif line.startswith('MAX'):
            m = ast.literal_eval(line[len('MAX '):])
    if c is None:
        rows.append((f, 'running')); continue
    for k, v in c.items():
        if k.startswith('max_') or k == 'prop6_max_bags_per_edge':
            mx[k] = max(mx[k], v)
        else:
            tot[k] += v
    for k, v in (m or {}).items():
        mx[k] = max(mx[k], v)
    fl = {k: v for k, v in c.items() if k.startswith('FAIL')}
    rows.append((f, '%d inst, %d tiles, %d Monge, %d e2e-Monge, fails %s' % (c.get('instances', 0), c.get('tiles', 0),
                 c.get('monge_checks', 0), c.get('e2e_monge_checks', 0), fl or 0)))
for r in rows:
    print('%-32s %s' % r)
print('TOTAL', {k: tot[k] for k in keys if k in tot})
print('FAILS-lines', {k: v for k, v in tot.items() if k.startswith('FAIL')}, 'run-level fails', fails)
print('MAX', {k: round(v, 3) for k, v in sorted(mx.items()) if 'H_ratio' not in k})
