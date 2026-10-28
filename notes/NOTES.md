# Candidates #16 and #17: exact SSSP and exact max flow in CONGEST

Started 2026-10-28. Literature checked on that date (arXiv, DROPS, author pages). Items marked
**~** are from memory and still need a look at the original paper.

## 1. State of the art

General graphs, n nodes, hop diameter D, polynomially bounded integer weights.

| Problem | Upper | Lower |
|---|---|---|
| Exact SSSP (directed, w ≥ 0) | Õ(√n + D + n^{2/5+o(1)}D^{2/5}) [2, 3]; Õ(√n·D^{1/4} + D) [4] | Ω̃(√n + D) |
| (1+ε)-SSSP, undirected | Õ(√n + D)·poly(1/ε) (tight) | Ω̃(√n + D) |
| (1+ε)-SSSP, directed | Õ(√n + D + n^{2/5+o(1)}D^{2/5})·poly(1/ε) [5] | Ω̃(√n + D) |
| Negative-weight SSSP | (√n + D + n^{2/5}D^{2/5})·n^{o(1)} [6] | Ω̃(√n + D) |
| Exact max flow / min-cost flow | n^{1/2+o(1)}(√n + D) [7] | Ω̃(√n + D) |
| (1+ε) max flow, undirected | (√n + D)·n^{o(1)} | Ω̃(√n + D) |

Planar graphs (lower bound Ω(D) for everything below):

| Problem | Upper |
|---|---|
| Exact SSSP, directed, w ≥ 0 | Õ(D²) [8] |
| (1+ε)-SSSP, directed | Õ(D/ε) [1] (June 2026; claimed deterministic, but its BDD is randomized) |
| Exact max st-flow, directed | Õ(D²) [9] (PODC 2025) |
| Dual SSSP with negative weights | Õ(D²) [9] |
| Directed global min cut | Õ(D²) [9] |

Two open questions are stated in the conclusion of [9]. The first is better primal SSSP, which
they call "the bottleneck to overcome in order to obtain better distributed planar algorithms".
The second is to "first improve the Õ(D²) bound of the (easier) directed SSSP problem (even with
non-negative weights)" before attacking max flow.

## 2. What the general-graph gaps actually are

### #16: exact SSSP is directed approximate SSSP

[3] (Lemma 3.1, Thm 1.7, App. C.1) reduces exact SSSP to O(log² n) calls of
(1+Θ(1/log n))-approximate SSSP on **directed** graphs. These calls go to the same edge set with
reweighted edges, and some come from a **virtual source** joined to every vertex with
nonnegative offsets. The reduction is deterministic and costs O(1) extra rounds per call in
CONGEST.

So CANDIDATES.md was too optimistic when it said "(1+ε)-approx is already tight". That holds
only for undirected graphs. In CONGEST, exact SSSP is as hard as directed (1+ε)-SSSP, up to
polylog factors, and the gap sits in the directed version.

The source of n^{2/5}D^{2/5} ([2], Sec. 5.2): skeleton framework with α skeleton nodes,
hop parameter n/α, plus a directed hopset on the skeleton with tradeoff ρ. The cost is

    n/α + αρ² + D·α^{1/2+o(1)}/ρ.

All three terms balance at α = n^{3/5}/D^{2/5} and ρ = D^{2/5}/n^{1/10}. The gap factor to
√n + D is largest at D = √n, where it is n^{1/10}. For D ≤ n^{1/4} or D ≥ n^{2/3} the bound is tight.

Barrier for this framework (my observation). Fix target T = Õ(√n) at D = √n. Then n/α ≤ T
forces α ≥ √n, D·β ≤ T forces hopbound β = Õ(1), and broadcasting the hopset forces size Õ(α).
The skeleton would need a directed (1+ε)-hopset of near-linear size with polylog hopbound.
Linear-size directed shortcut sets already need polynomial hopbound (Ω(n^{1/4}),
Bodwin-Hoppenworth 2023 **~**). So closing #16 needs a different framework, and the same
obstacle blocks parallel reachability. **Odds: low.**

### #17: exact max flow

The √n factor in [7] is the iteration count of a path-following interior point method; each
iteration is a Laplacian solve in (√n + D)·n^{o(1)} rounds. The sequential almost-linear-time
max flow algorithms use m^{1+o(1)} cheap iterations with dynamic data structures, and no
round-efficient counterpart is known. Negative-weight SSSP, a subroutine of the combinatorial
approaches, is as hard as reachability up to n^{o(1)} [6]. **Odds: low.**

## 3. Planar graphs: Theorem A

**Theorem A.** Let G be a planar digraph with nonnegative integer weights in
{0, …, n^{O(1)}}, hop diameter D, and source s. A CONGEST algorithm computes exact
distances from s and a shortest path tree in Õ(D) rounds w.h.p.

**Status: the algorithm is correct given Lemma 14′; the Õ(D) bound is open** (`LEMMA15.md`).
The labels (L) come from [1, Lemmas 15 and 16], whose topological core, [1, Lemma 14], is
false as stated (LEMMA15.md, (S7)). LEMMA15.md §3 proves Lemma 14′ with a new construction
(tiles). After the referee's fixes, a referee pass and two adversarial passes found nothing
wrong in it; no human has checked it. The second adversarial pass found that Property 6 of
[1, Lemma 9] is false for induced bags (LEMMA15.md, (S9)). Correctness does not use it, but
[1]'s Õ(D/ε) bound for the labels does, since it runs all bags of one depth in parallel.
Until that schedule is repaired, Theorem A is an exact algorithm whose Õ(D) round bound is
not proved. Theorems B, C and C′ inherit both points.

It is deterministic if the BDD is built deterministically. [1] calls itself deterministic,
but its BDD comes from Li-Parter, whose only random step is the Ghaffari-Parter separator
([9], adpw.txt 111-113 and 1417-1443). [1] cites deterministic separators (Jauregui-
Montealegre-Rapaport; Abd-Elhaleem-Dory-Weimann 2026) but never shows that they give a BDD
with Properties 1-7. The face identification needed for Ĝ is already deterministic
([9], App. A).

The previous bound was Õ(D²) [8]. The lower bound is Ω(D).

### Ingredients

- **(R) Reduction [3, App. C.1].** Exact SSSP needs O(log² n) oracle calls. Each call asks for
  (1+ε₀)-approximate distances, ε₀ = Θ(1/log n), from a source σ in a graph G' with
  nonnegative polynomially bounded integer weights. G' is G with reweighted edges, some edges
  deleted (cross-level edges in the level graphs H₁, H₂ of Def. 5.7), and σ is either s or a
  virtual vertex with an edge σ→u of weight φ(u) ∈ {0, …, poly} for every u. Everything
  outside the oracle is local: an edge needs the estimates at its two endpoints, which costs
  one round.
- **(L) Labels [1, Thm 9, Lemmas 15-16].** Take a BDD of the undirected network: height
  O(log n), bags X with spanning trees T_X of G[X] of diameter O(D log n) ([1] states T[X] of
  height O(D), but [8, Def. 4.1] only gives T[X] with O(log n) components; [8, Sec. 4.2]
  adds O(log n) edges), every edge in at most two bags per
  depth, leaf bags of size O(D log n), and Property 7(b), which says that every path in G[X]
  between different child bags meets the separator S_X. Let ∂S⁺_X be the hub set of bag X.
  In Õ(D/ε) rounds, every v ∈ X learns (1+ε)-approximations d̃_X(v,h) and d̃_X(h,v) of
  dist_{G[X]} for all h ∈ ∂S⁺_X. Hubs get these values from the oracle that is broadcast in
  X, and non-hubs from Lemma 16. Emulators never contract distances, so the estimates never
  underestimate.
- **Infinite distances.** The quasimetrics in [1] may contain ∞, but its Thm 1 and its LP
  handle only finite values. Directed G[X] has unreachable pairs. Fix: on every network edge,
  add each missing direction as an arc of weight M₂. The edge set and planarity stay the same,
  every distance becomes finite, and no estimate below M₂ changes.

### Lemma V (virtual source)

Given (L), (1+ε)-approximate distances from a virtual source with offsets φ take Õ(D/ε) rounds.

*Algorithm.*
1. For every bag X and h ∈ ∂S⁺_X, compute A_X(h) = min_{u∈X} φ(u) + d̃_X(u,h). This is a
   min-convergecast of |∂S⁺_X| = Õ(D) values over T_X, pipelined in Õ(D) rounds and
   broadcast back down. All bags of one depth run in parallel because edge congestion is
   at most 2 by Property 6, which is false for induced bags (LEMMA15.md, (S9)); this round
   count is open with it. Over all O(log n) depths this takes Õ(D) rounds.
2. Each leaf bag L gathers G[L] and φ|_L, as in the base case of [1, Lemma 16], and computes
   loc_L(v) = min_{u∈L} φ(u) + dist_{G[L]}(u,v) exactly.
3. Each v outputs d̃(v) = min( min_{leaves L ∋ v} loc_L(v), min_{X ∋ v, h ∈ ∂S⁺_X} A_X(h) + d̃_X(h,v) ).

*Proof.* **Upper bound.** Let u* be the vertex that attains d(σ,v) = φ(u*) + dist_G(u*,v),
with shortest path P*. Let Y be the deepest bag with P* ⊆ G[Y]; the root qualifies, so Y
exists.
- If Y is a leaf, then loc_Y(v) ≤ φ(u*) + |P*|.
- Otherwise P* is not inside one child of Y. A path that avoids S_Y has all of its vertices in
  a single child, because non-separator vertices lie in exactly one child (Property 7) and
  Property 7(b) applies. Such a path would also lie in that child's induced subgraph,
  contradicting the choice of Y. So P* contains some h ∈ S_Y ⊆ ∂S⁺_Y, and both of its subpaths
  lie in G[Y]. This gives A_Y(h) + d̃_Y(h,v) ≤ φ(u*) + (1+ε)|P*| ≤ (1+ε)·d(σ,v).

**Lower bound.** Every candidate value is at least
φ(u) + dist_{G[X]}(u,h) + dist_{G[X]}(h,v) ≥ φ(u) + dist_G(u,v), and loc_L(v) ≥ the same.
Hence d̃(v) ≥ d(σ,v). ∎

Note that the query must take the minimum over **all** common bags. In general, the lowest
bag that separates the two endpoints is not enough, since a shortest path can leave that bag.
Behind this sits a mismatch in [1]:
- Def. 4 says the labels store dist_G.
- Lemma 16 computes only dist_{G[X]}.
- The query in the proof of Thm 4 uses only the lowest separating bag.
- It has no case for two non-separator vertices in the same leaf, where no separating bag
  exists.

Lemma V covers both: the minimum over all common bags, and exact leaf-local terms. The fix costs
nothing. `sim/check.py` finds the single-bag query wrong on about 6% of random pairs.

Explicit counterexample (from the adversarial agent):
- **Decomposition.** The root separator is {a,b}, with children X = {s,a,b,c,u} and
  {w,a,b}. X has separator {c}, with children {s,a,c} and {u,b,c}.
- **Arcs.** s→a 1, a→w 1, w→b 1, b→u 1, a→c 100, c→u 1, s→c 100.
- **Result.** d(s,u) = 4 via w, which lies outside X. The query at X, with hubs {a,b,c} and
  G[X]-distances, returns 101.

*Lean.* `lean/SsspFlow/LemmaV.lean`, theorem `SsspFlow.Hierarchy.lemmaV`, builds without sorry
and depends only on the standard axioms (propext, Classical.choice, Quot.sound). What it proves:
- **Setting.** A digraph with arc lengths in [0, ∞], offsets φ, distances as infima over walks,
  and a well-founded bag hierarchy given by hub sets. The hypotheses are: a root bag holds every
  vertex; a non-hub vertex of a bag lies in exactly one child; and an arc between two non-hub
  vertices of a bag lies in a common child. With S_X ⊆ ∂S⁺_X these follow from Property 7(b).
- **Estimates.** For u, v ∈ X and h ∈ ∂S⁺_X, the estimates satisfy
  dist_{G[X]} ≤ d̃_X ≤ (1+ε)·dist_{G[X]}, in both directions.
- **Conclusion.** d(σ,v) ≤ d̃(v) ≤ (1+ε)·d(σ,v) for the all-bags query.
- **Leaves.** A leaf has no children, so the hypotheses make all of its vertices hubs. The
  leaf-local term is then the hub term with exact estimates.
- **Generality.** No finiteness is assumed.

The formalization does not cover the CONGEST algorithm or its round count, the construction of the
hierarchy and of the labels ([1, Lemma 16]), or the counterexample (that one is checked by
`sim/check.py`).

### Assembly

- **Oracle calls.** Each oracle call from (R) recomputes the labels (L) for the current
  weights and then runs Lemma V. There are two constants:
  - **M₁ > n·W_max: the offset.** A real source s becomes a virtual source σ₀ with
    φ(s) = 0 and φ = M₁ elsewhere. This makes every distance finite, which the potential
    argument of [3, Lemma 3.1] needs (Σ_u d(s,u) < ∞). An output ≥ M₁ means "unreachable";
    [6]'s oracle (Def. 24, Cor. 33) needs that distinction, and exactness makes it detectable.
  - **M₂ > (1+ε₀)·max φ ≥ M₁: the weight of deleted edges.** Since d(σ,·) ≤ max φ < M₂, no
    estimate below M₂ uses them, and the graph keeps the planar network's edge set.
- **Discretization ([3, App. C.1], sketched only there).** C.1 adds η = 1/poly to every edge,
  so smoothness holds for ℓ+η, and the Alg. 1 update can then drop an edge to −η. Fix: use
  ℓ_i + η as the base of every update, and bound the accumulated error by I·n·η < 1/6, so the
  final rounding is still exact. The call count is O(log n) Alg. 1 iterations × O(log n) calls
  in Alg. 3, i.e. O(log² n). (C.1's "O(log n)" undercounts.)
  *Lean* (`lean/SsspFlow/Boost.lean`, `Run.exact`; standard axioms, no sorry). The theorem
  assumes only the oracle contract on ℓ_i+η: the estimate is 0 at s, never below
  dist_{ℓ_i+η}, and smooth on every arc. It proves:
  - **Nonnegativity.** Every ℓ_i stays ≥ 0, so the oracle always sees lengths ≥ η.
  - **Contraction.** D_{i+1}(u) ≤ (1−1/α)·D_i(u) + (n−1)η holds at every vertex, so no sum
    over u is needed.
  - **Exactness.** Rounding is exact once (1−1/α)^I·D_0(u) + α(n−1)η < 1/2 and
    I(n−1)η < 1/2. With I ≥ α, the condition I·n·η < 1/6 above covers the η terms.
  - **Special case.** η = 0 is [3, Lemma 3.1].

  `c1_negative` gives the one-arc instance where C.1's base ℓ_i yields −η.
- **Round count.** O(log² n) calls × Õ(D/ε₀) = Õ(D). (R) and Lemma V are deterministic; (L) is
  deterministic except for the BDD (see the remark under Theorem A).
- **Tree.** Run the algorithm on w'(e) = n²·w(e) + 1. All weights are positive, so any
  tight in-edge per vertex gives a tree, and d(v) = ⌊d'(v)/n²⌋.

### Importance rating: modest to solid

Valuable as a statement, light as technique. [3, §3.1] already says its boosting works in any
model that can run the oracle.

- **What it does.** It closes the planar exact-SSSP gap up to polylog factors and answers the
  second open question of [9].
- **How much is new.** Little. The proof is about a page: a two-paper combination plus Lemma V.
- **Risks.**
  1. It depends on [1], which is four months old and unrefereed.
  2. The authors of [1] can be expected to notice this soon.
  3. [1, Lemma 14] is false as stated, so (L) is conditional on Lemma 14′ (LEMMA15.md).
  4. Property 6 of [1, Lemma 9] is false for induced bags, so the Õ(D/ε) round bound of (L)
     needs a new parallel schedule (LEMMA15.md, (S9)).

### Still to verify before anything goes public

Referee pass (agent, 2026-10-28): no error that breaks a result. Every bound in §3-5 holds
as a composition of the sources. Its points are folded into this file. Still open:

- **[1] Lemmas 14 and 15: (L) is conditional.** `LEMMA15.md` holds the repair. A referee pass
  and an adversarial pass (2026-10-28) reviewed its first draft.
  - **Analytic layer: proved and confirmed by both.** Lemmas 15′ and 16′ follow from a stated
    topological interface, Lemma 14′. The pieces are: the O′ witness for the LP, which stops
    the error from squaring per level; the triangle and all-orientation Monge constraints;
    rounding; gluing; and finiteness per component.
  - **Topological layer: proved, refereed once with the fixes in, and attacked twice, the
    second time on the fixed text.** [1, Lemma 14], that cutting the hub
    network merges all holes into one face, fails in three configurations consistent with
    Properties 1 to 7:
    1. separator chords in induced bags;
    2. virtual closing edges, where Def. 6 cuts a path with both ends on one face, which
       disconnects O_X;
    3. holes that meet at one vertex.

    In the first and third, no cyclic order makes the LP feasible (worst α* = 1.64 and 1.73).
    LEMMA15.md §3 replaces Def. 6 and Lemma 14 with tiles: the faces of a growing connected
    set Γ_d of corners of G (radial graph), with edges labelled by bag. Nothing is cut, so
    every tile is a disk. Children refine parents, ports per bag are O(D log n), and outside
    edges (at most 3|∂S*_X|) go straight into H_X. The prototypes ran 2.7 million Monge checks with
    every gluing planar, and the adversarial harness 1.55·10⁹ (M) inequalities on 24,850
    instances, with no failures (§3.7). The second adversarial pass added 14,500 instances
    with no failure in §3, and found (S9) in the assumptions.
  - **Realization: no longer needed from [1].** [10, Thm 1] (SODA 2025, refereed) proves
    that every quasimetric that is Monge for a prescribed circular order σ is realized by a
    plane digraph with O(|T|⁶) vertices and the terminals on the boundary in order σ. CONGEST
    does not charge for local computation, so centres find such a graph by exhaustive
    search. [1, Thm 2] would only make the local time polynomial, and its proof does not show
    the order guarantee.
- **[1] Lemma 9.** A deterministic BDD with Properties 1-7, if we want "deterministic".
- **More small gaps in [1]** (adversarial agent; all easy):
  - The LP of Thm 2 (lty 1265-1272) has no triangle-inequality constraints. Add them, or
    take the closure first.
  - Emulator weights are LP rationals, and the size of Thorup's oracle grows with log(aspect
    ratio). Round them; this is safe because all distances are ≥ 1 after the 1/poly shift.
  - [1] restates Property 7 as "at most three child bags", which clashes with "one child per
    component". Lemma 16(b) also silently uses "the first separator vertex on a path from v
    lies in v's child". Lemma V needs neither.

Adversarial pass (agent, 2026-10-28): it broke nothing, and its numerical runs had 0
failures: 300 Lemma V instances with adversarial (1+ε) overestimates, 600 Lemma D instances,
600 Theorem C instances and about 440 Theorem C′ instances. Its scripts are
`sim/attack/lemmaV.py` and `sim/attack/lemmaD_flow.py`.

Its verdict on novelty: [3, §3.1] says the boosting works in any model that can run the
oracle, which makes Theorem A close to folklore. The real additions are Lemma V and the query
fix.

## 4. Negative weights (Theorem B)

**Theorem B.** Let G be a planar digraph with polynomially bounded integer weights, possibly
negative, hop diameter D, and source s. A CONGEST algorithm either computes exact distances
from s or reports a negative cycle. It runs in D·(log n)^{O(√log n)} = D·n^{o(1)} rounds and is
correct w.h.p.

*Proof.* [6, Thm 2] gives (T(n,D) + √n + D)·(log n)^{O(√log n)} rounds from an oracle that
solves nonnegative SSSP from a virtual source in T(n,D) rounds.
- **Oracle.** All oracle calls are on G with reweighted edges, edges "deleted" by a high
  polynomial weight, and a virtual source ([6], Def. 24 and the proof of Cor. 58). Theorem A
  with Lemma V answers them in T = Õ(D). A virtual source inside the (R) reduction merges with
  the oracle's own virtual source into one offset vector, as in [6, Thm 26].
- **Where √n + D enters.** It comes only from [6, Thm 14], the simulation of
  minor-aggregation steps (Ghaffari-Zuzic). It is used in Cor. 27 (LDD), Cor. 33 (SCC and
  topological sort), Cor. 40 (FixDAGEdges) and the wrap-up of Cor. 58. Every other step is an
  oracle call or local computation.
- **Planar simulation.** On planar networks, part-wise aggregation takes Õ(D) through
  low-congestion shortcuts ([9, Cor. 4.6], Ghaffari-Haeupler). A minor-aggregation round
  therefore costs Õ(D) ([9, Lemma 4.8]).

**Negative cycles.** This needs no new argument. [6, Thm 60 / Alg. 5] already outputs
ERROR whenever there is a negative cycle, by checking the price function (Alg. 5, line 9).
Otherwise it computes distances w.h.p. Its other global steps (a few min/AND aggregations in
SPMain and EstDist) cost O(D). ∎

Rating: modest. This is a white-box substitution in [6].

## 5. Max flow (Theorems C, C′): the dual becomes a primal planar network

### Lemma D (weighted face-disjoint graph)

Let Ĝ be the face-disjoint graph of [9, Sec. 3], from Ghaffari-Parter. It has one star centre
per vertex and one region copy v_i per angle at v. Its edge sets are:
- **E_R.** Consecutive region copies along each face walk. Each face of G becomes its own
  E_R-cycle, and these cycles are vertex-disjoint.
- **E_C.** One edge per primal edge e, joining the two region copies at one endpoint that lie in
  the two faces on either side of e. This gives a 1-1 map to the dual edges (Prop. 5).
- **E_S.** The star edges.

By [9, Props 1-3], Ĝ is planar, has hop diameter ≤ 3D + 2 and at most 7n nodes, and any
r-round algorithm on Ĝ runs in 2r rounds on G. The bound 3D in [9] is between star centres;
corners are one hop further.

Give dual darts lengths λ (of any sign). Weight Ĝ as follows: 0 on both arcs of each E_R
edge; on each E_C edge, the two dual-dart lengths in their directions; M on both arcs of each
E_S edge, where M > 2·|V(Ĝ)|·max|λ|.

**Claim.** Ĝ has a negative cycle iff G* has one. If G* has none, then for any corners a ∈ g
and b ∈ h, dist_Ĝ(a,b) = dist_{G*}(g,h) whenever the right side is finite, and otherwise
dist_Ĝ(a,b) ≥ M/2. (The condition on negative cycles matters only when G* is not strongly
connected. In the Miller-Naor use every dual dart exists, so G* is strongly connected and a
negative cycle makes every dual distance −∞ anyway.)

*Proof.* The E_R-cycles have weight 0 in both directions. Contracting them preserves
distances between the contracted sets, and turns every face cycle into one node. Without the
star centres, the result is G* (Prop. 5). A path or cycle through a star centre uses two E_S
arcs, so it weighs ≥ 2M − |V(Ĝ)|·max|λ| > M. Shortest walks can be taken to be such paths and
cycles: with no negative cycle, cutting out closed subwalks does not increase weight, and a
negative closed walk contains a negative cycle. ∎

Ĝ is a multigraph, with two kinds of degenerate E_C edges:
- **Parallel edges.** At a degree-2 vertex, two E_C edges join the same corners.
- **Self-loops.** At a degree-1 vertex, the E_C edge is a self-loop (the dual of a bridge).
  A negative self-loop is a negative cycle; check it locally.

*Lean.* `lean/SsspFlow/LemmaD.lean` builds without sorry and depends only on the standard axioms.
- **Abstract version.** `Setup.negCycle_iff`, `Setup.walks` and `Setup.lemmaD` assume only the
  following about Ĝ:
  - each face's E_R arcs connect exactly that face's corners;
  - each dual dart has one E_C arc between corners of its two faces;
  - spokes run in both directions.

  Parallel arcs and loops are allowed. They prove the claim above, assuming M > |V(Ĝ)|·max|λ|
  (half the margin used here) and every face has a corner. They give dist_Ĝ ≥ M in place of
  M/2. Distances are infima over walks in EReal.
- **Combinatorial maps.** `rotSetup` builds Ĝ from a combinatorial map:
  - corners are darts;
  - faces are the orbits of φ;
  - E_R joins d to φ(d);
  - the edge {d, α(d)} gets its E_C arcs between d and φ(α(d)), at whichever dart is picked.

  `rot_pair` shows that both arcs of an edge join the same two corners (one E_C edge per edge),
  and `rot_lemmaD` is the claim for this Ĝ.
- **Planarity.** No step uses it, so the weighting works on any surface.

Not covered: planarity, the diameter bound and the 2× simulation [9, Props 1-3], and the
algorithms run on Ĝ.

[9, Prop. 5] already puts dual weights and directions on E_C. What Lemma D adds is the 0
weights on E_R, the M weights on E_S, and running primal algorithms on the result.

**Consequence.** This applies to distance problems: SSSP, virtual-source SSSP and
negative-cycle detection. It does **not** apply to problems that change when the zero-weight
E_R-cycles are contracted, such as girth (§6). Costs are a factor 2 in rounds, with D replaced
by 3D+2:
- Dual nonnegative SSSP: Õ(D) (Theorem A on Ĝ).
- Dual negative-weight SSSP: D·n^{o(1)} (Theorem B on Ĝ).

Before this, both were Õ(D²) [9, Lemma 2.2].

*Remark.* [9] uses Ĝ only to simulate minor aggregation, and treats it as unweighted. It builds
a separate dual BDD and dual labeling for SSSP, inside which face-parts are already glued with
zero-weight edges (adpw 2166, 2208, 2224). Lemma D extends that gluing to the whole graph. It is
a natural step rather than a new mechanism, but it makes the dual BDD unnecessary for distance
problems.

### Theorem C (exact max flow, directed planar)

Let G be a directed planar network with integer capacities in {0, …, poly(n)} and terminals
s, t. A CONGEST algorithm computes the maximum st-flow value and a flow assignment in
min{Õ(D²), D·n^{o(1)}} rounds, w.h.p. The previous bound was Õ(D²) [9, Thm 1.2]. The new term
wins once D ≥ n^{o(1)}, i.e. beyond (log n)^{O(√log n)}.

*Proof.* Use the Miller-Naor reduction exactly as in [9, Sec. 6.1].
- **Path P.** Find an s-t dart path P by BFS in O(D) rounds.
- **Binary search on λ.** There are O(log(nU)) steps. In each, residual dart capacities
  c − λ on P and c + λ on rev(P) are dual lengths, set locally. Run dual negative-weight SSSP
  with negative-cycle detection (Lemma D + Theorem B). A negative cycle means λ is infeasible.
- **Assignment.** f(d) = φ(h) − φ(g) ± λ·[d ∈ P or rev(d) ∈ P], where d* = (g, h). The
  endpoint of d knows the corners of g and h next to d, so this is local.

Directed min st-cut: run reachability in the residual graph, which is Theorem A with 0/1
weights, in Õ(D). ∎

### Theorem C′ (s, t on a common face: exact, Õ(D), w.h.p.)

This is the proof of [9, Thm 1.3] with an exact directed dual SSSP plugged in. [9] already
notes that Hassin works for directed graphs (adpw 2424-2427) and that exact distances give the
assignment (adpw 2395-2396).

Use Hassin's method, valid for darts and hence for directed graphs. Inside the common face f,
add a chord e = (t, s) with infinite capacity. It splits f into f₁ and f₂.
- **Lengths.** Dual dart lengths are the primal dart capacities; reverse darts have capacity 0.
- **SSSP.** Compute φ = dist from f₁ in G* − e*, with nonnegative lengths. f₁ must be the
  face on the left of the chord t→s (adpw ~2440); the other face computes the max t→s flow.
  `sim/check.py` uses F(t,s) in the networkx face convention. In Ĝ, f's
  E_R-cycle is cut into two paths, and the corners of s and t in f are split, all hosted
  locally. e* gets weight M.
- **Flow.** f(d) = φ(F₂(d)) − φ(F₁(d)) is a circulation in G + e. The triangle inequality gives
  0 ≤ f(d) ≤ c(d). Its value is f(e) = dist(f₁, f₂), which equals the capacity of the dual cut,
  so it is optimal.

This improves [9, Thm 1.3], which is (1−o(1))-approximate, undirected only, and runs in
D·n^{o(1)}.

### Ratings and dependencies

- **C: significant.** It brings the main theorem of a PODC'25 paper from Õ(D²) to D·n^{o(1)},
  which is near-optimal given Ω(D). The proof is entirely a composition, and it is only as
  sound as [1].
- **C′: modest.** It is [9]'s own proof with an exact oracle plugged in.
- **Lemma D: minor**, but it is the enabling observation.

Dependency chain (correctness of A, B, C, C′ rests on Lemma 14′; their round bounds also on a
repair of LEMMA15.md (S9)): [1] Thm 9 → Lemma V → (R) [3] → Theorem A → [6] + planar shortcuts →
Theorem B → Lemma D → Miller-Naor ([9, Sec. 6.1]).

### Numerical checks (`sim/check.py`)

Exact arithmetic on random planar instances (Delaunay with a third of the edges removed, 25-60
vertices). `python3 check.py 40 1` and `python3 check.py 40 7` pass, 80 instances in total.

- **Lemma V** (ε = 0, with a generic vertex-separator decomposition satisfying Property 7(b)):
  the formula equals the true virtual-source distances. The all-bags pairwise query is
  always exact. The single lowest-separating-bag query is wrong on 286 of 4800 random pairs,
  so the fix to the query of [1, Thm 4] is needed when layers store G[X]-distances.
- **Lemma D:** Ĝ is planar with diameter ≤ 3D. Distances equal dual distances (33
  instances), and negative cycles match (47 instances).
  - Ĝ is a **multigraph**: at a degree-2 vertex, both edges give an E_C edge between the same
    two corners. Keep the lighter parallel arc. Both corners sit on the same host, so this is
    local.
  - The first version of the script stored one arc per corner pair and failed on exactly this
    case.
- **Theorem C:** the Miller-Naor binary search on Ĝ finds the networkx max-flow value, and the
  assignment is feasible (80 instances).
- **Theorem C′:** chord, then Ĝ without the chord's E_R/E_C edges, then SSSP from F(t,s). The
  value f(t→s) equals max flow and the assignment is feasible (69 instances).

These checks test the sequential semantics only. They do not test round counts, or [1] itself.

## 6. Open after this

- **Directed planar global min cut** (Õ(D²) [9, Thm 1.5]). It needs the shortest *simple-dart*
  cycle in G*. Ĝ has zero-weight cycles, so girth on Ĝ is not the answer.
- **Weighted directed girth in planar digraphs** (Õ(D²), Parter).
- **Removing n^{o(1)} from Theorem C.** This would need a negative-weight reduction with
  polylog overhead.

## Sources

1. H. Le, H. Tierno, S. Yang. Planar Embedding of Okamura-Seymour Quasimetrics in Polynomial
   Time with an Application to Distributed SSSP. arXiv:2606.31192 (v2, July 2026).
2. N. Cao, J. T. Fineman. Parallel Exact Shortest Paths in Almost Linear Work and Square Root
   Depth. SODA 2023.
3. V. Rozhoň, B. Haeupler, A. Martinsson, C. Grunau, G. Zuzic. Parallel Breadth-First Search
   and Exact Shortest Paths and Stronger Notions for Approximate Distances. STOC 2023,
   arXiv:2210.16351.
4. S. Chechik, D. Mukhtar. Single-source shortest paths in the CONGEST model with improved
   bounds. PODC 2020.
5. N. Cao, J. T. Fineman, K. Russell. Brief announcement: an improved distributed approximate
   SSSP algorithm. PODC 2021.
6. V. Ashvinkumar et al. Parallel, Distributed, and Quantum Exact SSSP with Negative Edge
   Weights. ESA 2024, arXiv:2303.00811.
7. T. de Vos. Minimum Cost Flow in the CONGEST Model. arXiv:2304.01600.
8. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019.
9. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs.
   PODC 2025, arXiv:2411.11718.
10. Y. Chen, Z. Tan. Paths and Intersections: Characterization of Quasi-metrics in Directed
    Okamura-Seymour Instances. SODA 2025, arXiv:2410.19246.
