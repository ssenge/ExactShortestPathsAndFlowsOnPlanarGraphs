"""python3 -I run.py FAMILY SEEDS 'json-args' 'json-cfg'  -> per-seed stats + TOTAL"""
import sys, os, json, random, collections, time, traceback
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import PG, Fail
from geo import FAMS, virtual_candidates, drawing_ok
from engine import Engine
import post


def one(fam, seed, args, cfg):
    pos, E = FAMS[fam](seed, args)
    assert drawing_ok(pos, E), 'crossing edges in drawing'
    g = PG(pos, E, seed=seed)
    vc = virtual_candidates(pos, E) if cfg.get('virtual', True) else set()
    rng = random.Random(seed * 7919 + 1)
    eng = Engine(g, vc, rng, cfg)
    t0 = time.time()
    try:
        eng.run()
        if cfg.get('post', True):
            post.lemma16(eng, neg=cfg.get('neg'))
            post.e2e(eng, neg=cfg.get('neg'))
            post.prop6(eng)
            post.walk(eng)
    except Fail as ex:
        eng.st['FAILED'] += 1
        eng.fails.append(('exception', ex.args))
    eng.st['instances'] += 1
    eng.st['n_total'] += g.n
    eng.mx['n_max'] = max(eng.mx['n_max'], g.n)
    eng.mx['depth_max'] = max(eng.mx['depth_max'], getattr(eng, 'maxd', 0))
    eng.st['bags'] += len(eng.bags)
    eng.st['secs'] += round(time.time() - t0)
    return eng


if __name__ == '__main__':
    fam = sys.argv[1]
    seeds = range(*map(int, sys.argv[2].split(':'))) if ':' in sys.argv[2] else range(int(sys.argv[2]))
    args = json.loads(sys.argv[3]) if len(sys.argv) > 3 else {}
    cfg = json.loads(sys.argv[4]) if len(sys.argv) > 4 else {}
    tot = collections.Counter(); mx = collections.defaultdict(float); fails = []
    for s in seeds:
        try:
            eng = one(fam, s, args, cfg)
        except AssertionError as ex:
            tot['bad_instance'] += 1; continue
        tot.update(eng.st)
        for k, v in eng.mx.items():
            mx[k] = max(mx[k], v)
        if eng.fails:
            fails.append((s, eng.fails[:3]))
            print('SEED', s, 'FAILS', eng.fails[:3], flush=True)
    print('TOTAL', json.dumps(dict(tot), sort_keys=True))
    print('MAX', json.dumps({k: round(v, 3) for k, v in mx.items()}, sort_keys=True))
    print('FAILSEEDS', [f[0] for f in fails])
