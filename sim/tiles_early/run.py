"""Driver: python3 run.py <family> <seed0> <nseeds> [key=value ...]
families: see gens.FAMILIES (or 'mix'). keys: leaf=<int> allow7a=0/1 neg=0/1 e2e=0/1 wmode=small|unit|heavy|asym|binary
          strats=a,b,c inside=a,b  pextra=0,1  stop=0/1
Failing instances are pickled to fails/<family>_<seed>.pkl (P, bags, weights, fail info)."""
import sys, os, random, collections, pickle, time, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gens, bdd
from engine import Engine, CheckFail


def bdd_stats(bags, P, st):
    for b, B in bags.items():
        st['bags'] += 1
        if not B.get('kids'):
            st['leaves'] += 1
            continue
        st['nonleaf'] += 1
        st['sep_strat_' + B['strat']] += 1
        if B['closing'][0] == 'virtual':
            st['virtual_closings'] += 1
            if len(B['q']) == 2:
                st['digon_separators'] += 1
        else:
            st['real_closings'] += 1
        Xin = bags[B['kids'][0]]['X']
        if Xin == frozenset(B['S']):
            st['empty_interior'] += 1
        if not B['sat7a']:
            st['bags_violating_7a'] += 1
        st['max_out_comps'] = max(st['max_out_comps'], len(B['kids']) - 1)
        if B['pex'] > 0:
            st['extras_used'] += 1
        # pinch: S_X meets ancestors' separators in exactly one vertex
        p = B['parent']; anc = set()
        while p is not None:
            anc |= bags[p]['S']; p = bags[p]['parent']
        k = len(B['S'] & anc)
        if B['parent'] is not None:
            st['sep_meets_anc_0' if k == 0 else ('sep_meets_anc_1(pinch)' if k == 1 else 'sep_meets_anc_2+')] += 1
    st['max_depth'] = max(st['max_depth'], max(B['depth'] for B in bags.values()))
    # Property 6: every edge lies in at most two induced subgraphs of bags of one depth
    bydepth = collections.defaultdict(list)
    for b, B in bags.items():
        bydepth[B['depth']].append(B['X'])
    worst = 0
    for d, Xs in bydepth.items():
        cnt = collections.Counter()
        for X in Xs:
            for e, (a, c) in P.edges.items():
                if a in X and c in X:
                    cnt[e] += 1
        if cnt:
            worst = max(worst, max(cnt.values()))
    st['prop6_max_bags_per_edge'] = max(st['prop6_max_bags_per_edge'], worst)
    if worst > 2:
        st['prop6_violated_instances'] += 1


def main():
    fam = sys.argv[1]; s0 = int(sys.argv[2]); ns = int(sys.argv[3])
    kv = dict(a.split('=', 1) for a in sys.argv[4:])
    cfg = {}
    if 'leaf' in kv and kv['leaf'] != 'rand': cfg['leaf_size'] = int(kv['leaf'])
    if 'allow7a' in kv: cfg['allow7a'] = kv['allow7a'] == '1'
    if 'strats' in kv: cfg['strats'] = tuple(kv['strats'].split(','))
    if 'inside' in kv: cfg['inside'] = tuple(kv['inside'].split(','))
    if 'pextra' in kv: cfg['p_extra'] = tuple(float(x) for x in kv['pextra'].split(','))
    if 'preal' in kv: cfg['p_real'] = float(kv['preal'])
    if 'trees' in kv: cfg['tree_modes'] = tuple(kv['trees'].split(','))
    if 'global' in kv: cfg['global_tree'] = kv['global'] == '1'
    if 'region' in kv: cfg['region'] = kv['region'] == '1'
    if 'tries' in kv: cfg['tries'] = int(kv['tries'])
    opts = dict(neg=kv.get('neg') == '1', neg_e2e=kv.get('neg_e2e') == '1', e2e=kv.get('e2e', '1') == '1', stop=kv.get('stop', '1') == '1')
    if 'lp' in kv: opts['lp_samples'] = int(kv['lp'])
    opts['region'] = cfg.get('region', False)
    wmodes = kv.get('wmode', 'small,unit,heavy,asym,binary').split(',')
    tot = collections.Counter(); mx = collections.defaultdict(float)
    nfail = 0; t0 = time.time()
    os.makedirs(os.path.join(HERE, 'fails'), exist_ok=True)
    for seed in range(s0, s0 + ns):
        rng = random.Random(seed * 7919 + hash(fam) % 1000)
        f = rng.choice(sorted(gens.FAMILIES)) if fam == 'mix' else fam
        P = gens.FAMILIES[f](rng)
        gens.set_weights(P, rng, rng.choice(wmodes))
        c2 = dict(cfg)
        if kv.get('leaf') == 'rand':
            c2['leaf_size'] = rng.choice([2, 3, 4, 6, 10, 16])
        bags = bdd.build(P, rng, c2)
        bdd_stats(bags, P, tot)
        E = Engine(P, bags, rng, opts)
        try:
            E.run()
        except CheckFail as ex:
            nfail += 1
            print('FAIL seed', seed, f, ex.args[0], str(ex.args[1])[:300], flush=True)
            with open(os.path.join(HERE, 'fails', '%s_%d.pkl' % (fam, seed)), 'wb') as fh:
                pickle.dump(dict(P=P, bags=bags, fail=ex.args, family=f, seed=seed, cfg=cfg), fh)
        except Exception:
            nfail += 1
            print('ERROR seed', seed, f, flush=True)
            traceback.print_exc()
            with open(os.path.join(HERE, 'fails', '%s_%d_error.pkl' % (fam, seed)), 'wb') as fh:
                pickle.dump(dict(P=P, bags=bags, family=f, seed=seed, cfg=cfg), fh)
        tot.update(E.st)
        for k, v in E.mx.items():
            mx[k] = max(mx[k], v)
        tot['instances'] += 1
        tot['vertices'] += len(P.rot)
    print('FAMILY', fam, 'seeds', s0, s0 + ns - 1, 'fails', nfail, 'time %.0fs' % (time.time() - t0))
    keys = sorted(tot)
    print('COUNTS', {k: tot[k] for k in keys})
    print('MAX', {k: round(v, 3) for k, v in sorted(mx.items())})


if __name__ == '__main__':
    main()
