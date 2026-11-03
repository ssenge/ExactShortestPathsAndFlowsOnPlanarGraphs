# Negative weights and exact maximum flow in Õ(D) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/negative/`, elementary core in `lean/SsspFlow/NegScaling.lean`. Referee and adversary not yet run. No human has checked it. It rests on the Exact SSSP Theorem and the Label Hypothesis of [1], and on published black boxes of [2] and [3]. Importance: the bound is significant if [1] stands, the new mathematics is minor. Nearly all of the proof is the reduction of [2] with the algorithm of [1] as its oracle.

**A correction to [1].** The paper [1] lists the removal of the factor n^{o(1)} as open and says that it would need a reduction for negative weights with polylogarithmic overhead. That reduction was already published in [2], and our literature search missed it. The Negative Weights Theorem, part (b) of the Dual SSSP Corollary and the Maximum Flow Theorem of [1] are still correct as stated, but they are weaker than what follows from [1] and [2].

The model is CONGEST on a connected planar network with n vertices, hop diameter D and a known embedding. Õ hides factors polylogarithmic in n. Statement names are those of [1].

## 1. Results

**Theorem 1 (negative weights).** Let G be a planar digraph with integer weights of polynomial size, possibly negative, and source s. Given the Label Hypothesis, in Õ(D) rounds with high probability, either every vertex learns dist(s, v), or all vertices learn that G has a negative cycle. The algorithm also gives integer potentials φ with w(u, v) + φ(u) − φ(v) ≥ 0, which the vertices check locally, so an answer with distances is always right. A report of a negative cycle is wrong with probability at most n^{−c}.

**Theorem 2 (maximum flow).** Let G be a directed planar network with terminals s, t and integer capacities of polynomial size. Given the Label Hypothesis, every vertex learns the value of a maximum st-flow and the flow on each of its edges, and a minimum st-cut, in Õ(D) rounds with high probability. The output is certified by the cut, so it is always right.

**Corollary 3 (dual distances).** Part (b) of the Dual SSSP Corollary of [1] holds in Õ(D) rounds.

**Corollary 4 (fixed demands).** Let the network have integer capacities c(d) on darts and integer demands b(v) with sum 0, all of polynomial size. In Õ(D) rounds with high probability, every vertex learns a flow with net outflow b(v) at each v and f(d) ≤ c(d) on each dart, or all vertices learn that none exists.

**Corollary 5 (perfect matching, degrees).** In Õ(D) rounds with high probability: a perfect matching of a planar bipartite network, or the report that it has none; more generally a subgraph with prescribed degrees on a planar bipartite network; and an orientation of a planar network with prescribed out-degrees, or the report that it has none.

**Corollary 6 (minimum mean cycle).** Every vertex learns min_C w(C)/|C| over the cycles of a planar digraph in Õ(D) rounds with high probability.

All of these are given the Label Hypothesis. A path gives Ω(D) for Theorems 1 and 2, so these bounds are optimal up to polylogarithmic factors.

| Problem | Best before | Here |
|---|---|---|
| Exact SSSP, negative weights | Õ(D²) [5]; D·n^{o(1)} given the labels [1] | Õ(D) given the labels |
| Exact maximum st-flow, directed | Õ(D²) [5]; D·n^{o(1)} given the labels [1]; Õ(D) given the labels and (L3), `notes/MAXFLOW.md` | Õ(D) given the labels |
| Perfect matching, planar bipartite | Õ(D²) with no hypothesis, in the matching repo | Õ(D) given the labels |

**Relation to `notes/MAXFLOW.md`.** That note reaches the same bound for Theorem 2 by scaling over portals. It needs the extra hypothesis (L3), and in return it is deterministic relative to the labels. Theorem 2 needs no (L3), and it is randomized. Theorem 2 is the simpler route.

**What is new.** Little. The reduction is [2], its low-diameter decomposition and order are [3], the oracle is [1], and the corollaries are the reduction of [4]. We add the alternation of Lemma 1, which keeps every oracle call on the planar network, the merging of the calls, a self-contained form of the scaling with its behaviour on negative cycles, and two small repairs, listed in Section 8. Web searches on 3 Nov 2026 found no earlier statement of Theorem 1 or 2 with Õ(D) rounds, which is not proof that none exists. Such a statement needs an exact Õ(D) oracle for nonnegative weights, which earlier work did not have.

## 2. Tools

Write w_φ(u, v) = w(u, v) + φ(u) − φ(v). For a set of arcs, dist(V, v) is the least weight of a walk ending in v, the empty walk included. Let G≥0 be G with weights max(w, 0).

**(O), the oracle.** Given nonnegative integer weights of polynomial size on the arcs of a digraph on G, and integer offsets x ≥ 0 on a set S of vertices, every vertex learns min_{u ∈ S} (x(u) + dist(u, v)) in Õ(D) rounds. This is the algorithm Exact of [1, Algorithm 1], which runs on any new weights. To remove an arc, give it a weight above every value that matters. Vertices compute new weights from their own potentials with one round of exchange. It runs on the reversed arcs as well, and on the face-disjoint graph Ĝ of [1].

**(M), minor aggregation.** A step of the Distributed Minor-Aggregation Model takes Õ(D) rounds on planar networks [5, Cor. 4.6, Lemma 4.8].

**Lemma 2 (decomposition) [3, Lemma 4, Cor. 27; Lemma 5, Prop. 32, Cor. 33].** Given nonnegative integer weights of polynomial size and an integer d ≥ 1, with high probability, every vertex gets an integer index idx(v) of polynomial size, such that:

- vertices with equal index form a *cluster*, and any two u, v in a cluster have dist(u, v) ≤ d and dist(v, u) ≤ d in the whole graph with these weights;
- an arc is *cut* if it goes from a larger index to a smaller one, and it is cut with probability at most Q·w(e)/d + n^{−8}, with Q = O(log² n).

This takes Õ(1) calls of (O) and Õ(1) steps of (M). With E^rem = ∅ the same indices give the strong components in topological order, in O(log² n) calls of (O).

The set E^rem of [3, Lemma 4] is the set of removed arcs, and the clusters are the strong components without it, in the order of [3, Prop. 32], whose labels decrease along arcs, so idx is a constant minus the label. A cut arc lies in E^rem. In [3, Cor. 27], recursive calls on vertex-disjoint sets are merged into one call of (O), by a large weight on the arcs between the sets.

## 3. Few negative arcs

**Lemma 1 (alternation).** Fix a set of arcs of G with integer weights w, and integer potentials φ, all of polynomial size, and t ≥ 0. With t + 1 calls of (O) and t rounds, every vertex v gets d(v) such that d(v) is the weight of a walk ending in v, and d(v) ≤ w(P) for every walk P ending in v with at most t arcs negative in w_φ.

*Proof.* Let Pos be the arcs with w_φ ≥ 0. Let A_0(v) = min_x (−φ(x) + dist_Pos(x, v)), where distances use w_φ, and x runs over all vertices. Add a constant to make the offsets nonnegative, and subtract it afterwards. For i < t, let B_i(v) be the minimum of A_i(v) and of A_i(u) + w_φ(u, v) over negative arcs (u, v), one round. Let A_{i+1}(v) = min_x (B_i(x) + dist_Pos(x, v)), by one call. By induction, A_i(v) is the least value of −φ(x) + w_φ(P) over walks P from x to v with at most i negative arcs. Since w_φ(P) = w(P) + φ(x) − φ(v), this value is w(P) − φ(v). Put d(v) = A_t(v) + φ(v). ∎

## 4. The restricted problem

A digraph with integer weights is *restricted* if w(e) ≥ −1 and w(e) ≤ n for every arc, and w(C) ≥ |C| for every cycle C. Closed walks then satisfy the same inequality. This is [2, Def. 2.7]. The goal is potentials with w_φ ≥ 0.

**Lemma 3 (short paths in a cluster) [2, Lemma 3.2].** Let G be restricted, and let any two vertices of a set S have distance at most d in G≥0. Let P be a shortest path to v among paths in G[S] that start anywhere in S. Then P has at most d arcs, and max(w, 0)(P) ≤ d.

*Proof.* w(P) ≤ 0, since the empty path at v is a candidate. Let u be the start of P and let Q be a shortest path from v to u in G≥0, which may leave S. The closed walk C = P + Q has w(C) ≥ |C|. Also w(Q) ≤ max(w, 0)(Q) ≤ d. So |P| ≤ |C| ≤ w(C) ≤ d. Since max(w, 0)(e) ≤ w(e) + 1, max(w, 0)(P) ≤ w(P) + |P| ≤ d. ∎

**The algorithm [2, Algorithm 1].** Let L be least with 2^L ≥ 2n². Let R = (2 + c)·log₂ n and t = 4Q + 1. Let Φ_0 = {0}. For ℓ = 1, ..., L: for r = 1, ..., R, apply Lemma 2 to G≥0 with d = 2^ℓ, independently each time, and at ℓ = L once only and with no removed arcs. Then for each φ in Φ_{ℓ−1} apply Lemma 1 to the arcs inside clusters, to get d_φ. All clusters share these calls, since arcs between clusters are removed. Let φ_{ℓ,r}(v) = min_φ d_φ(v) − idx(v)·n. Let Φ_ℓ be the set of these potentials. Output the potential of level L.

**Proposition 4 [2, Theorem 3.1].** With high probability the output has w_φ ≥ 0 on all arcs. It takes Õ(1) calls of (O) and Õ(1) steps of (M), and all values are of polynomial size.

*Proof.* Fix ℓ > 1, r and v, with cluster S at (ℓ, r), and fix a shortest path P in G[S] from S to v. By Lemma 3, max(w, 0)(P) ≤ 2^ℓ, for ℓ = L too, since weights are at most n and any two vertices in one strong component have distance below n². Over the independent decomposition at (ℓ − 1, r′), the expected number of cut arcs on P is at most 2Q + n^{−7}, so at most t with probability at least 1/2. With R repetitions, and a union bound, with high probability each such P has a repetition r′ with at most t cut arcs. Call this the success event, and assume it.

For all levels we show: A(ℓ): for each r and each cluster S, min_φ d_φ(v) = dist_{G[S]}(S, v). B(ℓ): for each r, w_{φ_{ℓ,r}} ≥ 0 on each arc that is not cut at (ℓ, r).

A(1): by Lemma 3, P has at most 2 arcs, and t ≥ 2. B(ℓ − 1) gives A(ℓ): every d_φ is the weight of a walk in G[S], and G has no negative cycle, so d_φ(v) ≥ dist. For the repetition r′ of the success event, the arcs of P negative in w_{φ_{ℓ−1,r′}} are cut arcs, at most t of them, so Lemma 1 gives d_φ(v) ≤ w(P). A(ℓ) gives B(ℓ): inside a cluster, this is Johnson's observation for dist(S, ·). For an arc from index i to index j > i, let a, b be the values of min_φ d_φ at its ends. They lie in [−(n − 1), 0], since a path has at most n − 1 arcs of weight at least −1. So w + a − b + (j − i)n ≥ −1 − (n − 1) + n = 0.

At level L no arc is cut, so B(L) is the claim. Potentials are bounded by n + n·max idx. There are L·R decompositions, and L·R·|Φ|·(t + 1) calls for Lemma 1. ∎

## 5. Scaling

Let w be integer weights of polynomial size, and x = 2((n + 1)w + 1). Then x(C) ≥ 2|C| for every cycle if w has no negative cycle, and x(C) < 0 for a simple cycle with w(C) < 0.

**Lemma 5 (scaling).** Let x_φ ≥ −B with an integer B ≥ 1. Choose (ρ, α) = (⌈B/3⌉, 2) if B ≥ 5, (2, 1) if B is 3 or 4, (1, 1) if B = 2, and (1, 0) if B = 1. Let r = ⌊x_φ/ρ⌋ + α. If w has no negative cycle, then r has weights at least −1 and every cycle has r(C) ≥ |C|. If potentials ψ have r_ψ ≥ 0, then x_{φ+ρψ} ≥ −ρα. The value ρα is less than B in every case, so O(log nW) phases reach x_φ ≥ 0.

*Proof.* The floor of x_φ/ρ is at least −⌈B/ρ⌉, which is at least −(α + 1) in each case. For a cycle, ⌊y⌋ > y − 1 gives r(C) > x(C)/ρ + (α − 1)|C|. With α = 2, x(C) ≥ 0 suffices. With (2, 1), x(C)/2 ≥ |C|. With ρ = 1 the floor is exact, and r(C) = x(C) + α|C| ≥ 2|C|. Further, x_φ ≥ ρ⌊x_φ/ρ⌋ = ρ(r − α) ≥ ρ(ψ(v) − ψ(u) − α), which is the second claim. Finally 2⌈B/3⌉ < B for B ≥ 5. ∎

Arcs with r > n are dropped before Proposition 4 is applied, which keeps a restricted graph. One more call of (O) on the result gives dist(V, ·) in the graph without them. It is also dist(V, ·) for all arcs of r: a path with an arc above n has weight above n − (n − 1) > 0, and the empty path has weight 0. So this distance is a potential for all arcs of r. This is the note at the end of [2, Lemma 2.9].

*Negative cycles.* After each phase, the vertices check r_ψ ≥ 0 locally and aggregate the result in O(D) rounds, and they also check that values stay within the polynomial bound. If w has no negative cycle, all checks pass with high probability. If w has a negative cycle, then x has one, and no potentials exist for x, so some check fails. A failed check is reported as a negative cycle.

*Distances.* With x_φ ≥ 0, one call of (O) from s gives dist_x(s, v). For a walk, x(P) = 2(n + 1)w(P) + 2|P|. A least walk in x is simple and has least w among walks, and has at most n − 1 arcs. So dist(s, v) = ⌊dist_x(s, v)/(2(n + 1))⌋. The arcs tight in x form a shortest-path tree, since all cycles of x are positive. With offsets 0 on all vertices the same call gives dist(V, ·), which is a potential for w.

*Proof of Theorem 1.* O(log n) phases, each with Õ(1) calls of (O) and steps of (M), and each call takes Õ(D) rounds. ∎

## 6. Flow and the corollaries

*Corollary 3.* As in the proof of the Dual SSSP Corollary of [1]: run Theorem 1 on Ĝ with the lengths of its Dual Distance Lemma. Ĝ is planar with at most 7n nodes and hop diameter at most 3D + 2, and an r-round algorithm on it runs in 2r rounds on G. ∎

*Theorem 2.* As in the proof of the Maximum Flow Theorem of [1], with the reduction of [4]: binary search on β with a negative-cycle test by Corollary 3 in the dual with lengths c_β, O(log nU) tests. For the largest feasible β, the distances ψ give the flow ψ(lft d) − ψ(rgt d) + β[d ∈ P] − β[rev d ∈ P]. It is feasible by construction. Then one call of (O), with weight 0 on residual arcs, gives the set reached from s in the residual network. If t is not reached, this set is a cut with the value of the flow, and the output is right. Otherwise a test was wrong, which has probability at most n^{−c}, and the algorithm runs again. ∎

*Corollary 4.* This is [4]. Route b on a breadth-first tree: each tree edge gets the sum of b below it, in O(D) rounds, which gives a flow f_0 with net outflow b. A flow f with net outflow b is f_0 + g for a circulation g, and g(d) = ψ(lft d) − ψ(rgt d) for face potentials ψ. The condition f ≤ c is ψ(lft d) − ψ(rgt d) ≤ c(d) − f_0(d). By the two standard facts in [1, Section 5], this has a solution if and only if the dual with lengths c − f_0 has no negative cycle. Use Corollary 3. ∎

*Corollary 5.* Color the sides X and Y from a breadth-first tree, in O(D) rounds. For prescribed degrees g, set b = g on X and b = −g on Y, c(d) = 1 for darts from X to Y and c(d) = 0 for their reverses. An integer flow is the subgraph of the darts with f(d) = 1. The flow of Corollary 4 is an integer, since ψ is one. For perfect matching g = 1.

For out-degrees a(v), start from any orientation O_0. Reversing an arc from u to v moves one unit of out-degree from u to v. So set c(d) = 1 for the darts of O_0, c(d) = 0 for their reverses, and b(v) = outdeg_{O_0}(v) − a(v). The arcs to reverse are those with f(d) = 1. ∎

*Corollary 6.* The weights q·w − p have a negative cycle if and only if the minimum mean is below p/q. Two different means with cycle lengths at most n differ by at least 1/n². So O(log nW) tests with Theorem 1 find an interval of width below 1/n², which holds one fraction with denominator at most n. ∎

## 7. Costs

With the Q of [3], t = O(log² n), R = O(log n), L = O(log n): Lemma 1 runs L·R·|Φ| = O(log³ n) times with t + 1 calls each, so O(log⁵ n) calls per restricted problem, plus O(log² n) decompositions. With O(log n) phases of scaling this is O(log⁶ n) calls of (O) and more for the decompositions, and O(log n) more for the binary search of Theorem 2. These are large factors. Only their polylogarithmic form is claimed.

## 8. Two small points in [2]

Both have one-line repairs, and the proof above contains them.

- [2, Lemma 2.6] builds t + 1 layers where each crossing uses an arc, and it asks for the layer t. A path with fewer than t arcs does not reach this layer. The layered graph also is not planar, so we could not use it here in any case. Stay arcs of weight M repair it, and Lemma 1 does not need them.
- [2, Lemma 3.2] takes the return path Q in G[S], while the weak diameter holds in the whole graph. Lemma 3 above takes Q in the whole graph. The closed walk is still in the restricted graph.

## 9. Checks

`sim/negative/neg.py` runs all of the above centrally, with Dijkstra as the oracle, its own implementation of Algorithms 1 and 2 of [3], and the strong components and their order computed directly. The truth is Bellman-Ford, and `networkx` for flow and for matching.

No `FAIL` in any counter. The last number of each command is its time in seconds.

| Lane | What it runs | Runs | Compared with the truth | Max n | Other |
|---|---|---|---|---|---|
| `neg.py 1001 300`, `2001 300` | Proposition 4 with R = 3, t = 8 | 1,528 | 1,603,955 values of A(ℓ), 2,936,330 arcs of B(ℓ), no miss | 100 | 46,246 decompositions, 128 gave up, largest t needed 2 |
| `neg.py 1002 900 big` | same | 392 | 2,480,672 values, 4,624,731 arcs, no miss | 625 | 15,683 decompositions, 24 gave up, shortest paths up to 575 arcs, largest t needed 3, up to 271,079 oracle calls in a run |
| `neg.py scale 1003 300` | Lemma 5, with Bellman-Ford as the restricted solver | 155,945 | 2,615,081 distances, 29,921 instances with a negative cycle all reported | | 3,169,748 phases, B up to 38,563,838 |
| `neg.py full 1004 900` | Theorem 1, the whole stack | 130 | 2,112 distances, 36 instances with a negative cycle all reported | 49 | up to 1,077,679 oracle calls in a run |
| `neg.py flow 2005 420` | Theorem 2 and perfect matching, in the dual | 218 flows, 123 matchings | value against `networkx`, flow and cut checked; matching against Hopcroft-Karp | | 60 flows and 22 matchings on the whole stack, the rest with Bellman-Ford as the test; 116 instances have a perfect matching |

Every instance of Theorem 1 and Proposition 4 passes `nx.check_planarity`, and so does every flow and matching instance.

*The deterministic part of Proposition 4.* If at some level the success event fails, the proof says nothing, and otherwise it says that A(ℓ) and B(ℓ) are exact. With t and R far below the theory the event fails often, so this is testable, `neg.py event <seed> 300 <t> <R>`. A step counts as inexact if it misses in A or B.

| t, R | Runs | Event holds | Event fails | Runs with an inexact step | Wrong output | Inexact although the event holds |
|---|---|---|---|---|---|---|
| 2, 2 | 215 | 212 | 3 | 3 | 0 | 0 |
| 2, 1 | 423 | 382 | 41 | 41 | 1 | 0 |

In these runs the inexact steps and the failures of the event coincide exactly, which is more than the proof asks.

*Negative controls.* `neg.py ctl <seed> 40 [t]`, with R = 2 and the same instances. A control counts a wrong final potential.

| Control | What it changes | t = 2: wrong of runs | t = 1: wrong of runs |
|---|---|---|---|
| none | | 1 of 30 | 0 of 24 |
| `t0` | no alternation in Lemma 1 | 10 of 36 | 11 of 30 |
| `noprev` | potentials of the level before are ignored | 30 of 36 | 26 of 30 |
| `nooffset` | no shift by −idx·n | 12 of 36 | 20 of 30 |
| `wrongdir` | shift in the wrong direction | 11 of 30 | 18 of 24 |
| `nomin` | one potential in place of the minimum over Φ | 1 of 36 | 0 of 30 |
| `oneR` | one repetition per level | 0 of 59 | 0 of 63 |

The first four fire well above the clean rate. The single clean failure at t = 2 is what small t and R allow, and the lane above explains it. **`nomin` and `oneR` are weak controls.** They only lower a probability, and on these instances they are not told apart from the clean algorithm.

## 10. Not covered by the checks

- Rounds and messages: there is no CONGEST simulation.
- The Exact SSSP Theorem, the Label Hypothesis and all their caveats in [1] and `notes/LEMMA15.md`. Local computation is not polynomial, as there.
- Lemma 2 is a black box from [3]. We read its algorithms and its proof in CONGEST, and we implemented its algorithms, with the constant c = 1, which is far from the "sufficiently large" of its proof. So the simulation does not test the probability bound with its constants. It reports how often the decomposition gives up, and how many cut arcs a path has.
- The simulation uses t = 8 and R = 3 rather than t = 4Q + 1 and R = Θ(log n), so it is harder on the algorithm than the theorem. It also reports the smallest t that would have sufficed.
- The Lean file covers the arithmetic of Lemma 5, Lemma 1 for a given alternation, Lemma 3 and the arc inequality of Proposition 4. It does not cover the probabilities, Lemma 2, or the flow.
- Corollary 6 and the out-degree part of Corollary 5 are not simulated.

## References

1. S. Senge. Exact shortest paths and flows on planar graphs in CONGEST. This repository, tag `arxiv-v1`.
2. N. Fischer, B. Haeupler, R. Latypov, A. Roeyskoe, A. L. Sulser. A Simple Parallel Algorithm with Near-Linear Work for Negative-Weight Single-Source Shortest Paths. SOSA 2025, 216-225, arXiv:2410.20959.
3. V. Ashvinkumar, A. Bernstein, N. Cao, C. Grunau, B. Haeupler, Y. Jiang, D. Nanongkai, H. H. Su. Parallel, Distributed, and Quantum Exact Single-Source Shortest Paths with Negative Edge Weights. ESA 2024, arXiv:2303.00811.
4. G. L. Miller, J. Naor. Flow in planar graphs with multiple sources and sinks. SIAM J. Comput. 24(5), 1995.
5. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
