# Script test of naming, sides and the cut (2026-11-01)

This test tries to break, by simulation, concrete claims in the paper form of Theorem D: how the two
sides of γ are named, which copy of a new edge of Q lies on which side, how a cut is read from a path,
the direction in which a path is read, and the number of levels. A numerical check proves nothing; no
proof uses it. No claim failed.

`sim_copy.py` is a token-graph simulator written from the text of the paper, not from `thmD.py`. Lemma
names are those of the paper: the Incision Lemma is Lemma O of `notes/LEMMA_O.md`.

## Instances

Main lanes: 12,441,126 runs on 1,840,544 instances, 7,104,160 incisions, no abort and no crash.

- Every connected loopless map with m ≤ 7 edges: 5,224,794 runs, up to a cap of runs per instance.
- Random maps with 8 edges, mutated hard instances, the saved hard instances of `testR` and
  `testSO`, and planar families with many ties, up to 68 vertices, m = 33 and 7 levels.

Every negative control fired (a deliberately wrong rule that must fail), so the test is not silent.

## Results

| Claim | Checks | Failures |
|---|---|---|
| A1. One 0-piece and one 1-piece on every face of P | 31,145,656 faces | 0 |
| A1. δ and rev δ the right way round | 18,704,530 edges of P | 0 |
| A1. True sides by signed area; side 0 is the right of γ | 2,409,277 faces | 0 |
| A2. {(δ,1),(rev δ,2)} on the low side, {(δ,2),(rev δ,1)} on the high side | 15,606,515 new edges | 0 |
| A2. The same against a polygon oracle | 2,089,082 edges | 0 |
| A3. A called side is one subgraph | 12,755,678 | 0 |
| A3. A component is the called child of a side exactly when it holds a new edge of that side | 26,175,250 | 0 |
| A4. No node on both bounds | 25,196,804 annuli | 0 |
| A4. Labels match the bounds | 300,521,278 node checks | 0 |
| B. Every property of a computed walk W and its cut | 60,539,026 walks | 0 |
| B. A walk of least length gives a minimum cut (own Dinic) | 34,228,070 walks | 0 |
| C. Correct under every valid orientation, three variants | 383,626 runs each | 0 |
| D. Levels ≤ 1 + ⌈log2 m⌉ | all runs | 0 |
| D. Two ranges of a level share at most one index, an end of both | 11,990,441 pairs | 0 |

Details:

- **A2** covers x = y (6,093,839), x < y (4,743,179), x > y (4,769,497), Q of one edge (1,990,904) and
  of many (13,615,611), levels 1 to 6, and all 9 mode pairs. Modes change only Ĝ.
- **A2, value test.** Under the flipped rule, all 120,072 runs that finish still give the right value,
  and 70,033 others abort or crash. A test of the value alone therefore cannot validate this rule.
- **A3.** The 713,241 components with no new copy are exactly the cases of Q without a new edge. Uncalled
  sides can have at least 5 components, so the rule depends on the call flags.
- **B** covers x = y (23,418,748), x < y (18,722,452), x > y (18,397,826), overlap walks (6,184,556)
  and loops (9,257,410). The bound c'(U) ≥ c'(P[p_t,p_x]) was always an equality. Only repair paths
  reach the minimum in 4,358 runs.
- **C.** Roots g⁰ and g¹ give different Q on 252,010 of 2,763,615 comparisons because of ties, and both
  are correct. The smallest simple instance found has n = 4. Reading from g⁰ matters in two ways.
  Unreversed, the literal y is undefined (921,205 of 921,205). With δ taken at the start of the reading
  instead of at the g_x end, all 386,922 stored-pair checks fail and 143,428 of 383,626 runs abort or
  crash.

The statement that the part holding (rev δ,2) holds (δ',1) is false: it failed on 153,148 of 9,191,703
checks at nodes with three parts (same side, different piece). The proof of the Incision Lemma does not
use it.

**Values per face.** Of the pieces named by an annulus, 19% (2,422,691 of 12,769,593) lie outside its
range, which the indices i_1 and i_2 allow. The paper derives O(1) values per face from the sharing of
ranges. This holds, since [18, Lemma 5.5] computes P_m only for m in the range of the annulus, so a
piece outside the range carries no value. Measured with those pieces included: at most 2 annuli per
p_t^σ and at most 3 per face.

## Not covered

- Round counts, distributed aggregation, mark-and-bisect, flags as messages.
- E_C edges, weights, rotations, planarity and hop diameter of Ĝ.
- The merge of parallel edges: multi-maps run unmerged with enlarged N and K; simple graphs use the
  formulas of the paper exactly.
- Real identifiers of Ĝ: ties in trees use a seeded hash.
- Sizes beyond 68 vertices, m = 33 and 7 levels. For m = 8 the maps are sampled, and m = 5 to 7 use
  limited capacity vectors.
- Complete enumeration of ties: runs are capped, 2,153 corner choices did not finish, and the planar
  lanes sample ties.
- Non-convex faces and dual loops in the polygon lane (244,387 runs skipped for A1 and 254,128
  incisions for A2).
- Some checks ran in separate lanes only: 951,795 runs, no failure.

## Reproduce

```
sh lanes1.sh; sh lanes1b.sh; sh lanes2.sh; sh lanes3.sh
python3 -I aggregate.py
```

The merged counts are in `logs/agg_main.txt`, `agg_exh.txt`, `agg_C_all.txt` and `agg_ctl.txt`.
`t_smoke.py` runs the 11-vertex instance on which the unrepaired recursion reports 37 for a minimum
cut of 15; here it gives 15.
