"""Scaling of vertex/edge multiplicity per depth on the degree-3 expansion.
python3 scale.py CONF FAM 'json-args' SEEDS"""
import sys, os, json, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
from gadget import expand
from gsweep import vmult
from comm import probe
from sweep import CONF
from geo import FAMS, virtual_candidates, drawing_ok
from core import PG
from engine import Engine
conf, fam, args, ns = sys.argv[1], sys.argv[2], json.loads(sys.argv[3]), int(sys.argv[4])
res = collections.defaultdict(float); cnt = 0
for s in range(ns):
    pos, E = FAMS[fam](s, args)
    P, EE, _ = expand(pos, E)
    if not drawing_ok(P, EE):
        continue
    g = PG(P, EE, seed=s)
    cfg = dict(CONF[conf]); cfg['leaf'] = 8
    eng = Engine(g, virtual_candidates(P, EE), random.Random(s * 7919 + 1), cfg)
    try:
        eng.run()
    except Exception:
        res['fail'] += 1; continue
    o, m = probe(eng); m.update(vmult(eng)); cnt += 1
    for k in ('mult_induced', 'mult_comm', 'vmult_all', 'vmult_phantom', 'commdiam_over_GXdiam'):
        res[k] = max(res[k], m[k])
    res['depth'] = max(res['depth'], eng.maxd); res['n'] = max(res['n'], g.n)
print(conf, fam, args, cnt, {k: round(v, 2) for k, v in res.items()}, flush=True)
