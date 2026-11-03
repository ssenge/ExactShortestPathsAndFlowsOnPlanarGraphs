"""Tightness probe: for every child check, record (a_Y, h(X), h(Y), c(X), c(Y)) and report the largest h at
which B3 (a_Y = max(1,h)+1), B4 (h(Y) = h(X)+1) and B2 (c(Y) = c(X)+a_Y with a_Y >= 2) hold with equality.
python3 -I tight.py CONF START:END fams scale"""
import sys, os, random, collections, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import adv
from adv import *
import engine_r9, engine_c9

REC = collections.defaultdict(lambda: (-1, None))


def patch(cls):
    orig = cls.lp46
    def lp46(self, b, res):
        orig(self, b, res)
        X = self.bags[b]; cX = self.comps_T(X['X'], X['E']); hX = self.holes_euler(X['E'])
        for i, Y in enumerate(res['kids']):
            aY = self.arcs_R(res['q'], res, i); cY = self.comps_T(Y, res['kidsE'][i]); hY = self.holes_euler(res['kidsE'][i])
            key = (self._tag, b, i, X['depth'], res['real'], res['kinds'][i])
            if aY == max(1, hX) + 1 and hX > REC['B3'][0]:
                REC['B3'] = (hX, dict(where=key, aY=aY, hX=hX))
            if hY == hX + 1 and hX > REC['B4'][0]:
                REC['B4'] = (hX, dict(where=key, hX=hX, hY=hY))
            if aY >= 2 and cY == cX + aY and aY > REC['B2'][0]:
                REC['B2'] = (aY, dict(where=key, cX=cX, cY=cY, aY=aY))
            if aY > REC['aYmax'][0]:
                REC['aYmax'] = (aY, dict(where=key, aY=aY, hX=hX))
    cls.lp46 = lp46


patch(engine_r9.Engine)
if __name__ == '__main__':
    conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':')); fams = sys.argv[3].split(','); scale = float(sys.argv[4])
    for s in range(a, b):
        r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]
        args, pos, E = build(fam, s, r, scale)
        if len(pos) < 12 or not drawing_ok(pos, E):
            continue
        try:
            g = PG(pos, E, seed=s)
        except AssertionError:
            continue
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10]); cfg['light'] = True
        P_ = np.asarray(pos, float); A_ = P_[[x for x, y in E]]; B_ = P_[[y for x, y in E]]
        vc = {pr for pr in virtual_candidates(pos, E) if not seg_cross(P_[pr[0]], P_[pr[1]], A_, B_, eps=0.0)}
        eng = Engine(g, vc, random.Random(s * 7919 + 1), cfg)
        eng._tag = (conf, fam, s, json.dumps(args))
        try:
            eng.run()
        except Fail as ex:
            print('FAIL', fam, s, ex.args)
    for k, v in REC.items():
        print(k, v)
