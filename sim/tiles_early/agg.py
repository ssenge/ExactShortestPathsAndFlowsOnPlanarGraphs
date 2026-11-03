"""aggregate logs given as arguments: python3 agg.py logs/a7_*.log"""
import sys, ast, collections
tot = collections.Counter(); mx = collections.defaultdict(float); fails = 0
for f in sys.argv[1:]:
    for line in open(f):
        if line.startswith('FAMILY'):
            w = line.split(); fails += int(w[w.index('fails') + 1])
        elif line.startswith('COUNTS'):
            for k, v in ast.literal_eval(line[7:]).items():
                if k.startswith('max_') or k.startswith('prop6_max'): mx[k] = max(mx[k], v)
                else: tot[k] += v
        elif line.startswith('MAX'):
            for k, v in ast.literal_eval(line[4:]).items(): mx[k] = max(mx[k], v)
keys = ['instances','vertices','nonleaf','tiles','monge_checks','lp_checks','e2e_components','e2e_monge_checks','T4b_glue_checks','wheel_tau_checks','H_wheel_checks','T5_order_checks','T5_class_checks','rank_face_checks','claim4_checks','claim4b_checks','claim5_checks','claim7_vertex_checks','claim7_J_checks','virtual_closings','digon_separators','empty_interior','sep_meets_anc_1(pinch)','q_all_outside','q_edges_outside','bag_no_own_edges','P_used','bags_violating_7a','claim7_vertex_checks_7a_violated','prop6_violated_instances']
print('files', len(sys.argv) - 1, 'runfails', fails, {k: tot[k] for k in keys if tot[k]})
print('FAILS', {k: v for k, v in tot.items() if 'FAIL' in k or 'region' in k})
print('T5dirs', {k: v for k, v in tot.items() if k.startswith('T5_dir')})
mx.pop('e2e_H_ratio', None); print('MAX', {k: round(v, 2) for k, v in sorted(mx.items())})
