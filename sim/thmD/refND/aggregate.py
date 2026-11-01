"""Merge the lane logs: python3 -I aggregate.py [pattern...]; prints verdict tables per claim."""
import sys, os, json, glob, collections, math
LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs')
def load(fs):
    C = collections.Counter(); F = {}; EX = {}; lev = {}; mm = [0,0,0]; metas = []
    for fn in fs:
        d = json.load(open(fn))
        C.update(d['counts'])
        for k, v in d['fails'].items():
            if k not in F or tuple(v['size']) < tuple(F[k]['size']): F[k] = v
        for k, v in d['examples'].items():
            if k not in EX or tuple(v['size']) < tuple(EX[k]['size']): EX[k] = v
        for k, v in d['levels_by_m'].items():
            lev[int(k)] = max(lev.get(int(k), 0), v)
        mm = [max(mm[0], d.get('max_range_mult', 0)), max(mm[1], d.get('max_piece_mult', 0)), max(mm[2], d.get('max_face_annuli', 0))]
        metas.append((os.path.basename(fn), d['counts'].get('runs', 0), d['counts'].get('instances', 0), d['secs'], d.get('final'), d.get('stopped_early')))
    return C, F, EX, lev, mm, metas
def show(title, fs):
    C, F, EX, lev, mm, metas = load(fs)
    print('=' * 8, title)
    for m in metas: print('  ', m)
    print('  runs', C['runs'], 'instances', C['instances'], 'incisions', C['a3.incisions'], 'abort', C['abort'], 'crash', C['crash'], 'enum_incomplete', C['enum_incomplete'])
    fails = {k: v for k, v in C.items() if k.startswith('FAIL')}
    print('  FAILS', fails)
    groups = collections.defaultdict(lambda: [0, 0])
    for k, v in C.items():
        if k.endswith(' #chk'):
            name = k[:-5]
            groups[name][0] += v
            groups[name][1] = C.get('FAIL ' + name, 0)
    for pref in ('a1.', 'mode.', 'a2.', 'a3.', 'a4.', 'b.', 'c23.', 'd.', 'j.', 'o.', 'q.', 'inv.'):
        print('  --', pref)
        for k in sorted(groups):
            if k.startswith(pref): print('     %-55s chk %12d fail %8d' % (k, groups[k][0], groups[k][1]))
    print('  -- controls')
    for k in sorted(C):
        if k.startswith('ctl') and k.endswith('#chk'):
            base = k[:-5]
            print('     %-40s chk %12d caught %12d (%.1f%%)' % (base, C[k], C[base + ' #caught'], 100 * C[base + ' #caught'] / max(1, C[k])))
    print('  -- strata and stats')
    for k in sorted(C):
        if k.startswith(('a2.chk','a3.','q.','b.stat','b.winner','b.rule_winner','b.min_cp','c.','d.','stat.','mode.s','mode.t','overlap','a1.','a4.','o.old','ties.','cap_paths','fam.','cap.','a2.parity')) and not k.endswith('#chk') and not k.startswith('FAIL'):
            print('     %-55s %12d' % (k, C[k]))
    print('  -- levels by m', {m: lev[m] for m in sorted(lev)})
    if lev:
        worst = max(lev, key=lambda m: lev[m] / max(1e-9, math.log2(m + 1)) if m else 0)
        print('     max levels', max(lev.values()), 'max m', max(lev), 'worst ratio levels/log2(m+1)', worst, lev[worst], round(lev[worst] / math.log2(worst + 1), 3))
    print('     max #live ranges holding one index', mm[0], '; max #annuli holding a piece of one p_t^sigma', mm[1], '; of one face p_t', mm[2])
    print('  -- smallest failing instances')
    for k, v in sorted(F.items()):
        print('     ', k, v['size'], json.dumps(v['inst']), 'f,g,cs,ct', v['f'], v['g'], v['cs'], v['ct'], 'seq', v['seq'], 'level', v['level'], v['detail'][:300])
    print('  -- examples')
    for k, v in sorted(EX.items()):
        print('     ', k, v['size'], json.dumps(v['inst']), 'f,g,cs,ct', v['f'], v['g'], v['cs'], v['ct'], 'seq', v['seq'], 'level', v['level'], v['detail'][:300])
if __name__ == '__main__':
    if len(sys.argv) > 1:
        for p in sys.argv[1:]:
            show(p, sorted(glob.glob(os.path.join(LOG, p))))
    else:
        main = [f for f in sorted(glob.glob(os.path.join(LOG, '*.json'))) if not os.path.basename(f).startswith(('t_', 'ctl', 'C.'))]
        show('main lanes (no controls, no reading variants)', main)
