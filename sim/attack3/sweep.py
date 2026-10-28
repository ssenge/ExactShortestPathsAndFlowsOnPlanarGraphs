"""python3 -I sweep.py CONFIG START:END [families]  -- random family parameters per seed."""
import sys, os, json, random, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from run import one

MODES_ALL = {"bal": 2, "bnd": 1, "avoid": 1, "virt": 1, "onG": 1, "chord": 1, "rand": 1, "long": 0.5}
CONF = {
    # LP-faithful: z only inherited, inside = bounded side, BFS-based T_X, no degenerate bags
    'faithful': dict(modes={"bal": 3, "bnd": 1, "virt": 1, "onG": 1, "rand": 1}, zall=0.0, swap=0.0,
                     degenerate=False, txmode='bfs', tries=120),
    'mixA': dict(modes=MODES_ALL, zall=0.5, swap=0.3, degenerate=False, txmode=['bfs', 'bfs', 'dfs', 'rand'], tries=120),
    'mixB': dict(modes=MODES_ALL, zall=1.0, swap=0.5, degenerate=True, txmode=['bfs', 'dfs', 'rand'], tries=120),
    'px': dict(modes={"avoid": 6, "bal": 1}, zall=0.3, swap=0.3, degenerate=False, txmode=['bfs', 'dfs', 'rand'],
               tries=400, bal=0.97),
    'pxc': dict(modes={"avoid": 8, "bal": 1}, zall=0.3, swap=0.0, degenerate=False, txmode=['bfs', 'bfs', 'dfs'],
                tries=600, bal=0.99, root='center'),
    'pxf': dict(modes={"avoid": 10, "bal": 1}, zall=0.3, swap=0.3, degenerate=False, txmode='bfsfar',
                tries=600, bal=0.99),
    'strict': dict(modes={"bal": 3, "bnd": 1, "virt": 1, "onG": 1, "rand": 1}, zall=0.0, swap=0.0,
                   degenerate=False, txmode='bfs', tries=200, strict=True),
    'ch': dict(modes={"chord": 4, "bnd": 1, "bal": 1}, zall=1.0, swap=0.3, degenerate=True, txmode=['bfs', 'rand'], tries=200),
}


def params(fam, r):
    if fam == 'dl': return dict(n=r.randint(40, 170), drop=r.choice([0.0, 0.2, 0.4]))
    if fam == 'grid': return dict(k=r.randint(6, 13), drop=r.choice([0.0, 0.15, 0.3]))
    if fam == 'k2m': return dict(m=r.randint(12, 90), chord=r.random() < 0.8, sub=r.choice([1, 1, 2, 3]))
    if fam == 'fan': return dict(k=r.randint(12, 40), extra=r.randint(4, 20))
    if fam == 'nested': return dict(R=r.randint(3, 6), K=r.randint(8, 20), p=r.choice([0.2, 0.35, 0.6]))
    if fam == 'pend': return dict(n=r.randint(15, 30), k=r.choice([2, 3, 4]))
    if fam == 'flower': return dict(k=r.randint(4, 11), L=r.randint(3, 7))
    raise KeyError(fam)


if __name__ == '__main__':
    conf = sys.argv[1]
    a, b = map(int, sys.argv[2].split(':'))
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    tot = collections.defaultdict(collections.Counter); mx = collections.defaultdict(lambda: collections.defaultdict(float))
    fails = []
    t0 = time.time()
    for s in range(a, b):
        r = random.Random(s * 31 + 7)
        fam = fams[s % len(fams)]
        args = params(fam, r)
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14])
        try:
            eng = one(fam, s, args, cfg)
        except AssertionError as ex:
            tot[fam]['bad_instance'] += 1; continue
        tot[fam].update(eng.st)
        for k, v in eng.mx.items():
            mx[fam][k] = max(mx[fam][k], v)
        if eng.fails:
            fails.append((fam, s, args, eng.fails[:2]))
            print('FAIL', fam, s, args, eng.fails[:2], flush=True)
    for fam in tot:
        print('FAM', fam, json.dumps(dict(tot[fam]), sort_keys=True))
        print('MAX', fam, json.dumps({k: round(v, 3) for k, v in mx[fam].items()}, sort_keys=True))
    print('NFAILS', len(fails), 'secs', round(time.time() - t0))
