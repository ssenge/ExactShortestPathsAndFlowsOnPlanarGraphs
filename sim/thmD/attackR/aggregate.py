"""Sum the counters of the final deep runs (no control variant) and print totals."""
import json, collections, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
L = os.path.join(HERE, 'logs')
RUNS = ['deep_A_mix_default', 'deep_B_big_default', 'deep_C_litchord', 'deep_D_litfull', 'deep_E_kissc',
        'deep_F_kissc_lit', 'e2e_gen_kiss', 'e2e_gen_touch', 'e2e_gen_random', 'e2e_gen_avoid', 'e2e_tie_kiss',
        'search_e2e_n4_12', 'search_simple', 'sssp_mix', 'ctl_none']
T = collections.Counter()
per = {}
for r in RUNS:
    d = json.load(open(os.path.join(L, r + '.json')))
    c = collections.Counter(d['counts'])
    if 'inst' in c and 'instances' not in c:
        c['instances'] = c['inst']
    T.update(c)
    per[r] = dict(args=d.get('args'), secs=d.get('secs'), instances=c.get('instances'), levels=c.get('levels'),
                  bad={k: v for k, v in c.items() if k.startswith('BAD')})
for r, v in per.items():
    print(r, v)
keys = ['instances', 'levels', 'defR_levels', 'N_annuli_checked', 'N_nodeparts_checked', 'N_orphans_checked',
        'N3_pieces_refined', 'RuleM_tokens_incised_anew', 'RuleM_endpoint_edge_incised_anew', 'RuleM_X_tokens',
        'Pi_computed', 'leaf', 'children', 'overlap', 'overlap_full_only', 'child_discarded_overlap',
        'child_range_empty', 'orphan_range', 'orphan_ov', 'orphan_range_with_Pt_pair', 'i12_outside_range',
        'case_ii_nodes', 'case_iv_nodes', 'case_iv_old_old', 'case_iv_old_new', 'case_iv_new_old', 'case_iv_new_new',
        'Qedges_new', 'Qedges_old', 'cov_endpoint_edge_in_I_modeL', 'cov_endpoint_edge_in_I_modeR',
        'cov_endpoint_edge_in_I_deg1', 'cov_endpoint_edge_in_I_deg2', 'cov_endpoint_edge_in_I_deg3',
        'cov_endpoint_edge_incised_anew', 'cov_e0_eq_elast_incised_LL', 'cov_e0_eq_elast_incised_RR', 'cov_X_deg3',
        'LV_residual_components', 'LV_residual_with_bad', 'LV_residual_with_full_bad_only', 'LV_orphan_component',
        'F3_mismatch_c_ov1', 'F3_mismatch_f_ov1', 'e2e_checked', 'e2e_all_paths_unique', 'sssp_levels',
        'sssp_nodeparts_checked', 'pick_fallback_bfs']
print('TOTAL')
for k in keys:
    print('  %s %d' % (k, T.get(k, 0)))
for k in sorted(T):
    if k.startswith('max_level_'):
        print('  %s %d' % (k, T[k]))
print('  BAD', {k: v for k, v in T.items() if k.startswith('BAD')})
