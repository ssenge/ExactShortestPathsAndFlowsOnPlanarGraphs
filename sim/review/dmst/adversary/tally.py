# Adds up the counters of the lanes. The controls are not counted as runs. The first family run (outC, with the
# 64-bit guard hit on 6 instances) is replaced by the rerun in outE.
import re, sys, collections
tot = collections.Counter()
lanes = collections.defaultdict(collections.Counter)
maxima = collections.Counter()
for fn in ['outB.txt', 'outC.txt', 'outD.txt', 'outE.txt', 'outF.txt']:
    cur = None
    for line in open(fn):
        m = re.match(r'(EXH|RND-COR|RND|HILLF|HILL|FILE) ', line)
        if m:
            cur = m.group(1)
            if fn == 'outC.txt' and cur == 'FILE':
                cur = 'SKIP'
        if not (m or line.startswith(' cov') or line.startswith(' checks')):
            continue
        if cur in (None, 'SKIP'):
            continue
        for k, v in re.findall(r'([A-Za-z_0-9>=]+?)=(\d+)(?:\s|$)', line):
            if k == 'max_steps':
                maxima[k] = max(maxima[k], int(v))
                lanes[cur]['max_steps'] = max(lanes[cur]['max_steps'], int(v))
            elif k != 'secs':
                tot[k] += int(v)
                lanes[cur][k] += int(v)
for name in sorted(lanes):
    L = lanes[name]
    print(f"{name:8s} runs={L['runs']:>11,} active_runs={L['active_runs']:>11,} steps={L['steps']:>11,} active_comps={L['active_comps']:>11,} calls={L['calls']:>11,} max_steps={L['max_steps']} FAILS={L['FAILS']}")
print('TOTAL runs', f"{tot['runs']:,}", 'active', f"{tot['active_runs']:,}", 'steps', f"{tot['steps']:,}", 'active_comps', f"{tot['active_comps']:,}", 'calls', f"{tot['calls']:,}", 'FAILS', tot['FAILS'], 'max_steps', maxima['max_steps'])
keys = ['multi_active', 'partial_K', 'd_inf_member', 'd_eq_beta_noncycle', 'same_tail_two_members', 'beta0', 'tied_beta_arcs', '2cycle_one_edge', '2cycle_two_edges', 'antipar_in_K', 'mutual_K1_K2', 'K_to_rootcomp', 'nest>=3', 'pi_arcs', 'pi_internal_hops', 'hops_on_edge_without_arc', 'hops_on_heavy_edge', 'pi_trivial', 'pi_last_arc_is_chosen_of_c', 'neg_in_arc_r', 'arcs_from_unreached', 'small_reach', 'rho_trees>=2', 'rho_chosen', 'empty_branching', 'brute', 'lemma3', 'seq', 'subtree', 'level', 'left_out_on_cycle', 'sv_strong', 'sv_not_strong', 'dual_steps']
for k in keys:
    print(f'  {k:32s} {tot[k]:>16,}')
lem = collections.Counter()
for fn in ['outA.txt']:
    for line in open(fn):
        if line.startswith('lem '):
            print(line.strip()[:200])
        if line.startswith(' FAILS'):
            print(line.strip())
        for k, v in re.findall(r'(instances|states|contractions|T_in_L2|T_in_L3|eq|L4|d_inf|partial|d_eq_beta_noncycle|pi_last_arc_is_chosen_of_c)=(\d+)', line):
            lem[k] += int(v)
print('LEMMA TOTAL', dict(lem))
