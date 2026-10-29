"""Lemma O checks (thmD_R) on the 25 saved instances of the adversarial search, many run seeds."""
import sys, os, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD_R as T
LOGS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attackR', 'logs')
hits = [h for f in ('search_simple.json', 'search_e2e_n4_12.json') for h in json.load(open(os.path.join(LOGS, f)))['hits']]
nruns = int(sys.argv[1])
tot = collections.Counter(); st = collections.Counter(); fails = []
for h in hits:
    I = dict(n=h['n'], ends=[tuple(e) for e in h['ends']], rot=h['rot'], cap=h['cap'], s=h['s'], t=h['t'])
    for r in range(nruns):
        for tb in ('minid', 'random'):
            for rule in ('formal', 'anycorner'):
                opts = dict(mode='claimed', variant='fixed', tiebreak=tb, pairs=1, pcommon=0.0,
                            pfar=(r % 3) / 2.0, e0rule=rule, ends=1, lemO=1)
                chk, info = T.run_one(I, opts, 104729 * r + 17)
                tot['runs'] += 1
                for k, v in info.items():
                    if isinstance(k, str) and k.startswith(('O', 'R_')) and isinstance(v, int):
                        st[k] += v
                bad = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
                if bad:
                    fails.append(dict(seed=h['seed'], r=r, tb=tb, rule=rule, flags=dict(chk.flags)))
print(json.dumps(dict(runs=tot['runs'], nfail=len(fails), fails=fails[:5],
                      stats={k: st[k] for k in ('O_incisions', 'O_c23_chk_core', 'O_INV_checked', 'O_node_linear',
                                                 'O_pred_end_old_Pa', 'O_pred_end_old_Pb', 'O_both_bounds',
                                                 'R_full_z', 'R_full_neq')})))
