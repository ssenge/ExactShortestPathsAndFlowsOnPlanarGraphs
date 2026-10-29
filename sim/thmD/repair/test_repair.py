"""Test harness for Lemma R (notes/GHAT_REPAIR.md).

usage: python3 -I test_repair.py RULE START COUNT [size grid]
RULE: formal  = thmD's D3 rule (L preferred, mirrored R fallback)
      anylegal = uniform over all legal (corner in p0, mode) pairs, L or R
Wraps thmD.build_ghat; every G^_l built with variant 'fixed' is also built from the formal
definition (formal_ghat.build_formal) and checked.
"""
import sys, os, collections, random, inspect, json, time, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.dirname(HERE)]  # repair/ and sim/thmD/
import thmD
import formal_ghat as FGm

CNT = collections.Counter()
NOTES = []
STATE = {}


def note(k, v=None):
    CNT[k] += 1
    if v is not None and len(NOTES) < 30:
        NOTES.append((k, v))


def bfs(adj, src, cap):
    dist = {src: 0}
    q = collections.deque([src])
    while q:
        x = q.popleft()
        if dist[x] >= cap:
            continue
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1
                q.append(y)
    return dist


def check_level(emb, Gf, annuli, level):
    # ---- copies per vertex
    per = collections.Counter(k[1] for k in Gf.verts)
    term = {cu['v'] for cu in Gf.cuts}
    for v in range(emb.n):
        lim = 3 * emb.deg(v) + (2 if v in term else 1)
        if per[v] > lim:
            note('P4_copies_exceed', (v, per[v], lim))
        if v not in term and per[v] > 3 * emb.deg(v) + 1:
            note('P4_copies_nonterminal_exceed')
    CNT['max_copies_minus_3deg'] = max(CNT['max_copies_minus_3deg'], max(per[v] - 3 * emb.deg(v) for v in range(emb.n)))
    # ---- planarity of the explicit rotation
    r = FGm.check_rotation(Gf)
    if not r[0]:
        note('P3_rotation_bad', r[1])
    else:
        _, V, E, F, conn = r
        if not conn:
            note('P3_disconnected')
        if V - E + F != 2:
            note('P3_euler_fail', (level, V, E, F))
        else:
            CNT['P3_euler_ok'] += 1
    # ---- property 1: E_R components == pieces
    pcs = FGm.pieces(emb, Gf)
    tok2piece = {}
    for pi, (f, cyc, seq) in enumerate(pcs):
        for x in seq:
            assert x not in tok2piece
            tok2piece[x] = pi
    if set(tok2piece) != set(Gf.toks):
        note('P1_tokens_vs_pieces')
    radj = collections.defaultdict(list)
    for (a, b, typ, info, h) in Gf.E:
        if typ == 'R':
            radj[a].append((b, info))
            radj[b].append((a, info))
    vpiece = {}
    for k in Gf.verts:
        if k[0] == 'S':
            if radj[k]:
                note('P1_sigma_has_ER')
            continue
        ps = {tok2piece[x] for _, x in radj[k]}
        if len(ps) != 1:
            note('P1_vertex_in_%d_pieces' % len(ps), (level, k))
            continue
        vpiece[k] = ps.pop()
        if len(radj[k]) > 2:
            note('P1_degree_gt2', k)
    # each piece: path / cycle structure
    for pi, (f, cyc, seq) in enumerate(pcs):
        vs = set()
        for x in seq:
            vs.add(Gf.alpha[x])
            vs.add(Gf.beta[x])
        if cyc:
            if len(vs) != len(seq):
                note('P1_cycle_not_simple', (level, pi))
        else:
            if len(vs) != len(seq) + 1:
                note('P1_path_not_simple', (level, pi, seq))
            # consecutive tokens share a vertex
        for a_, b_ in zip(seq, seq[1:] + ([seq[0]] if cyc else [])):
            if Gf.beta[a_] != Gf.alpha[b_]:
                note('P1_consecutive_not_linked', (level, a_, b_))
    # ---- property 2: E_C
    npairs = 0
    for (a, b, typ, info, h) in Gf.E:
        if typ != 'C':
            continue
        npairs += 1
        x, y = info
        if vpiece.get(a) != tok2piece[x] or vpiece.get(b) != tok2piece[y]:
            note('P2_ec_wrong_ends', (level, info, a, b))
        if a[1] != h or b[1] != h:
            note('P2_ec_not_local')
    want = sum(2 if (e in Gf.I) else 1 for e in range(emb.m))
    if npairs != want:
        note('P2_ec_count', (npairs, want))
    # ---- Fact N + closedness against the live annuli
    piece_key = {}
    for pi, (f, cyc, seq) in enumerate(pcs):
        if cyc:
            piece_key[frozenset(seq)] = pi
        else:
            piece_key[tuple(seq)] = pi
    np2piece = {}
    for A in annuli:
        aset = set()
        for X in A.nodes.values():
            aset |= set(X.seq)
        for X in A.nodes.values():
            k = frozenset(X.seq) if X.cyc else tuple(X.seq)
            if k not in piece_key:
                note('FactN_fail', (level, X))
            else:
                np2piece[(A.aid, X.id)] = piece_key[k]
            for x in X.seq:
                if FGm.partner(x) not in aset:
                    note('closedness_fail')
    # ---- distances: every copy within 2 of its sigma, sigma-sigma <= 4 per edge of G
    adj = collections.defaultdict(list)
    for (a, b, *_r) in Gf.E:
        if a != b:
            adj[a].append(b)
            adj[b].append(a)
    for v in range(emb.n):
        dv = bfs(adj, ('S', v), 4)
        for k in Gf.verts:
            if k[1] == v and dv.get(k, 99) > 2:
                note('P4_copy_far', k)
        nb = {emb.tl[d ^ 1] for d in emb.rot[v]}
        for u in nb:
            if dv.get(('S', u), 99) > 4:
                note('P4_sigma_far', (v, u))
    # ---- property 6: token-based local correspondence to level-1
    prev = STATE.get('prev')
    if prev is not None and annuli:
        palpha, pbeta, pI, pvpiece, ppcs, pnp_pieces, ptoks = prev
        ptokset = set(ptoks)
        for A in annuli:
            for X in A.nodes.values():
                gs = set()
                parents = set()
                for x in X.seq:
                    d, l = x
                    xp = x if (d >> 1) in pI else (d, 0)
                    if xp not in ptokset:
                        note('P6_parent_token_missing', (level, x))
                        continue
                    parents.add(xp)
                    for w in (emb.tl[d], emb.tl[d ^ 1]):
                        a = Gf.alpha[x] if emb.tl[d] == w else Gf.beta[x]
                        ap = palpha[xp] if emb.tl[d] == w else pbeta[xp]
                        gs.add(pvpiece.get(ap))
                        if a[0] == 'X' or ap[0] == 'X':
                            CNT['P6_X_copy_matched'] += 1
                if len(gs) != 1 or None in gs:
                    note('P6_ambiguous', (level, X.id, gs))
                    continue
                g = gs.pop()
                if not parents <= set(ppcs[g][2]):
                    note('P6_parent_not_superset', (level, X.id))
                if g not in pnp_pieces:
                    note('P6_parent_not_annulus_nodepart', (level, X.id))
                CNT['P6_checked_nodeparts'] += 1
    STATE['prev'] = (Gf.alpha, Gf.beta, set(Gf.I), vpiece, pcs, set(np2piece.values()), list(Gf.toks))
    # ---- stats on degenerate cases
    for cu in Gf.cuts:
        c = (cu['v'], cu['ci'])
        CNT['cut_mode_' + cu['mode']] += 1
        if cu['e0'] in Gf.I:
            CNT['e0_incised_' + cu['mode']] += 1
        if emb.deg(cu['v']) <= 2:
            CNT['terminal_deg%d' % emb.deg(cu['v'])] += 1
            if cu['e0'] in Gf.I:
                CNT['e0_incised_at_deg%d_terminal_%s' % (emb.deg(cu['v']), cu['mode'])] += 1
    if len(Gf.cuts) == 2 and Gf.cuts[0]['e0'] == Gf.cuts[1]['e0']:
        CNT['e0_eq_elast' + ('_incised' if Gf.cuts[0]['e0'] in Gf.I else '')
            + '_' + Gf.cuts[0]['mode'] + Gf.cuts[1]['mode']] += 1
    pv = STATE.get('prevI')
    for cu in Gf.cuts:
        if pv is not None and cu['e0'] in pv and cu['e0'] not in Gf.I:
            CNT['e0_unincised_again'] += 1
        if pv is not None and cu['e0'] not in pv and cu['e0'] in Gf.I:
            CNT['e0_newly_incised_' + cu['mode']] += 1
    STATE['prevI'] = set(Gf.I)
    if any(h is not None and a == b for (a, b, typ, info, h) in Gf.E if typ == 'C'):
        CNT['ec_selfloop_level'] += 1
    for k in Gf.verts:
        if k[0] == 'X':
            r = Gf.rot[k]
            CNT['X_deg%d' % len(r)] += 1


ORIG_BUILD = thmD.build_ghat


def wrapped(emb, incised, epts, variant='literal'):
    Gc = ORIG_BUILD(emb, incised, epts, variant)
    if variant != 'fixed':
        return Gc
    fr = sys._getframe(1).f_locals
    if 'active' in fr and 'A1' in fr:
        annuli = list(fr['active'])
        level = fr.get('level')
    else:
        annuli = [fr['A0']]
        level = 0
        STATE['prev'] = None
        STATE['prevI'] = None
    cuts = [dict(v=ep['v'], ci=ep['ci'], mode=ep['mode'], e0=ep['e0']) for ep in epts]
    try:
        Gf = FGm.build_formal(emb, incised, cuts)
        if FGm.edge_multiset(Gf) != FGm.code_multiset(Gc):
            note('DEF_mismatch_with_code', level)
        else:
            CNT['DEF_match'] += 1
        check_level(emb, Gf, annuli, level)
    except Exception:
        note('harness_exception', traceback.format_exc()[-800:])
    CNT['levels_checked'] += 1
    return Gc


thmD.build_ghat = wrapped

# ---- run_reif variant with the 'anylegal' endpoint rule
src = inspect.getsource(thmD.run_reif)
old = "        formal = [i for i in cs if (emb.rot[v][i] >> 1) not in Pedges]\n"
assert old in src
new = ("        if opts.get('e0rule') == 'anylegal':\n"
       "            dv = emb.deg(v)\n"
       "            leg = [(i, 'L') for i in cs if (emb.rot[v][i] >> 1) not in Pedges]\n"
       "            leg += [(i, 'R') for i in cs if (emb.rot[v][(i + 1) % dv] >> 1) not in Pedges]\n"
       "            assert leg, 'P5: no legal endpoint choice'\n"
       "            i, md = rng.choice(leg)\n"
       "            ee = emb.rot[v][i] >> 1 if md == 'L' else emb.rot[v][(i + 1) % dv] >> 1\n"
       "            return dict(v=v, ci=i, mode=md, e0=ee)\n") + old
src = src.replace(old, new)
src = src.replace('def run_reif(', 'def run_reif_any(')
exec(compile(src, 'run_reif_any', 'exec'), thmD.__dict__)


def run_one(I, opts, seed):
    emb = thmD.inst_emb(I)
    chk = thmD.Checker()
    info = {}
    rng = random.Random(seed)
    try:
        thmD.run_reif_any(emb, I['s'], I['t'], opts, rng, chk, info)
    except thmD.Fail as ex:
        chk.flag('fail_exception', str(ex))
    except AssertionError:
        chk.flag('impl_assert', traceback.format_exc()[-600:])
    return chk, info


def main():
    rule, start, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if len(sys.argv) > 5:
        thmD.SIZE_MAX, thmD.GRID_MAX = int(sys.argv[4]), int(sys.argv[5])
    opts = dict(mode='claimed', variant='fixed', tiebreak='random', pairs=1, pcommon=0.3, pfar=0.5, e0rule=rule)
    nbad = 0
    t0 = time.time()
    for sd in range(start, start + count):
        I = thmD.make_instance(sd, None)
        chk, info = run_one(I, opts, sd * 7919 + 1)
        bad = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
        if bad:
            nbad += 1
            note('THMD_FLAG', (sd, dict(bad), [str(x)[:200] for x in chk.notes[:3]]))
        CNT['instances'] += 1
    print(json.dumps(dict(rule=rule, start=start, count=count, thmD_bad=nbad, secs=round(time.time() - t0),
                          counts=dict(sorted(CNT.items())), notes=[str(x)[:400] for x in NOTES]), indent=1))


if __name__ == '__main__':
    main()
