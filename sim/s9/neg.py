"""Negative controls for the region form: original rule 3 must trip 'R: owned edge not a region edge';
a corrupted Lemma 16' recursion must be detected; shuffled port orders must break Monge."""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
from sweep import CONF, params
from geo import FAMS, virtual_candidates
from core import PG, Fail
from engine_r import Engine
import post_r
fams = ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
cnt = collections.Counter()
for s in range(int(sys.argv[1]), int(sys.argv[2])):
    r = random.Random(s * 31 + 7); fam = fams[s % 7]; args = params(fam, r)
    pos, E = FAMS[fam](s, args); g = PG(pos, E, seed=s)
    for kind in ('rule3orig', 'l16', 'shuffle'):
        cfg = dict(CONF['ch']); cfg['leaf'] = 8
        if kind == 'rule3orig': cfg['rule3orig'] = True
        if kind == 'shuffle': cfg['neg'] = 'shuffle'; cfg['stop'] = False
        eng = Engine(g, virtual_candidates(pos, E), random.Random(s), cfg)
        try:
            eng.run()
            if kind == 'l16':
                post_r.lemma16(eng, neg='l16')
        except Fail as ex:
            cnt[(kind, ex.args[0])] += 1; continue
        if kind == 'l16': cnt[('l16 detected', eng.st['neg_L16_detected'] > 0)] += 1
        if kind == 'shuffle': cnt[('shuffle detected', eng.st['neg_monge_detected'] > 0)] += 1
        if kind == 'rule3orig': cnt[('rule3orig passed', True)] += 1
for k, v in sorted(cnt.items(), key=str):
    print(k, v)
