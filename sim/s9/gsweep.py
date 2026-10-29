"""Like comm.py, on the bounded-degree expansion of each family instance. Adds vertex multiplicities."""
import sys, os, random, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
import comm
from comm import probe
from gadget import expand
from sweep import CONF, params
from geo import FAMS, virtual_candidates, drawing_ok
from core import PG
from engine import Engine


def vmult(eng):
    mx = collections.Counter()
    for d in range(len(eng.levels)):
        lab = eng.levels[d]['label']
        ownv = collections.defaultdict(set)
        for e, Y in enumerate(lab):
            for x in eng.g.ends[e]:
                ownv[x].add(int(Y))
        cnt = collections.Counter(); ph = collections.Counter()
        for b, B in eng.bags.items():
            if B['depth'] != d:
                continue
            for x in B['X']:
                cnt[x] += 1
                ph[x] += b not in ownv[x]
        if cnt:
            mx['vmult_all'] = max(mx['vmult_all'], max(cnt.values()))
            mx['vmult_phantom'] = max(mx['vmult_phantom'], max(ph.values()))
    return mx


if __name__ == '__main__':
    conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':'))
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    tot = collections.defaultdict(collections.Counter); mx = collections.defaultdict(lambda: collections.defaultdict(float))
    for s in range(a, b):
        r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]; args = params(fam, r)
        pos, E = FAMS[fam](s, args)
        P, EE, own = expand(pos, E)
        if not drawing_ok(P, EE):
            tot[fam]['bad_drawing'] += 1; continue
        g = PG(P, EE, seed=s)
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14])
        eng = Engine(g, virtual_candidates(P, EE), random.Random(s * 7919 + 1), cfg)
        try:
            eng.run()
        except Exception as ex:
            tot[fam]['engine_fail'] += 1; continue
        o, m = probe(eng)
        m.update(vmult(eng))
        tot[fam].update(o); tot[fam]['n'] += g.n
        for k, v in m.items():
            mx[fam][k] = max(mx[fam][k], v)
    for fam in tot:
        print(fam, dict(tot[fam]))
        print('   ', {k: round(v, 2) for k, v in mx[fam].items()})
