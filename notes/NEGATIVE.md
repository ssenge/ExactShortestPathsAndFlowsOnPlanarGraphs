# Negative weights and exact maximum flow in Õ(D) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/negative/`, elementary core in `lean/SsspFlow/NegScaling.lean`. The first bullet of Lemma 2 comes from a corollary in [3] that is false as stated, and it is repaired in Section 8. No human has checked it. It rests on the Exact SSSP Theorem and the Label Hypothesis of [1], on a known embedding, and on published black boxes of [2], [3], [4] and [5]. Importance: modest. The bound would be significant, but only given the Hypothesis, whose local computation is not polynomial, and the new mathematics is minor. Nearly all of the proof is the reduction of [2] with the algorithm of [1] as its oracle.

**A correction to [1].** The paper [1] lists the removal of the factor n^{o(1)} as open and says that it would need a reduction for negative weights with polylogarithmic overhead. That reduction was already published in [2], and the paper missed it. The Negative Weights Theorem, part (b) of the Dual SSSP Corollary and the Maximum Flow Theorem of [1] are still correct as stated, but they are weaker than what follows from [1] and [2].

The model is CONGEST on a connected planar network with n vertices, hop diameter D and a known embedding. Õ hides factors polylogarithmic in n. Statement names are those of [1].

## 1. Results

**Theorem 1 (negative weights).** Let G be a planar digraph with integer weights of polynomial size, possibly negative, and source s. Given the Label Hypothesis, in Õ(D) rounds with high probability, either every vertex learns dist(s, v), or all vertices learn that G has a negative cycle. The algorithm also gives integer potentials φ with w(u, v) + φ(u) − φ(v) ≥ 0. An answer with distances passes the local checks of Proposition 7, so it is always right. A report of a negative cycle is wrong with probability at most n^{−c}, and Proposition 7 also removes this error, with O(log nW) more tests.

**Theorem 2 (maximum flow).** Let G be a directed planar network with terminals s ≠ t and integer capacities of polynomial size. Given the Label Hypothesis, every vertex learns the value of a maximum st-flow and the flow on each of its edges, and a minimum st-cut, in Õ(D) rounds with high probability. The output passes the local checks of Proposition 7, so it is always right.

**Corollary 3 (dual distances).** Part (b) of the Dual SSSP Corollary of [1] holds in Õ(D) rounds.

**Corollary 4 (fixed demands).** Let the network have integer capacities c(d) on darts and integer demands b(v) with sum 0, all of polynomial size. In Õ(D) rounds with high probability, every vertex learns a flow with net outflow b(v) at each v and f(d) ≤ c(d) on each dart, or all vertices learn that none exists.

**Corollary 5 (perfect matching, degrees).** In Õ(D) rounds with high probability: a perfect matching of a planar bipartite network, or the report that it has none; more generally a subgraph with prescribed degrees on a planar bipartite network; and an orientation of a planar network with prescribed out-degrees, or the report that it has none.

**Corollary 6 (minimum mean cycle).** Every vertex learns min_C w(C)/|C| over the cycles of a planar digraph, or that it has no cycle, in Õ(D) rounds with high probability.

All of these are given the Label Hypothesis. A path gives Ω(D) for Theorems 1 and 2, so these bounds are optimal up to polylogarithmic factors.

| Problem | Best before | Here |
|---|---|---|
| Exact SSSP, negative weights | Õ(D²) as stated in [6, Sec. 1.1], [5] has the dual statement; D·n^{o(1)} given the labels [1] | Õ(D) given the labels |
| Exact maximum st-flow, directed | Õ(D²) [5]; D·n^{o(1)} given the labels [1]; Õ(D) given the labels and (L3), `notes/MAXFLOW.md` | Õ(D) given the labels |
| Perfect matching, planar bipartite | Õ(D²) with no hypothesis, in the matching repo | Õ(D) given the labels |

**Relation to `notes/MAXFLOW.md`.** That note reaches the same bound for Theorem 2 by scaling over portals. It needs the extra hypothesis (L3), and in return it is deterministic relative to the labels. Theorem 2 needs no (L3), and it is randomized. Theorem 2 is the simpler route.

**The core without the Hypothesis.** This note uses [1] only through (O). So any (O) that takes T rounds gives negative weights in Õ(T + D) rounds, and any (O) on Ĝ that takes T rounds gives Theorem 2 in Õ(T + D) rounds. That part survives even if the Hypothesis falls.

**What is new.** Little. The reduction is [2], its low-diameter decomposition and order are [3], the oracle is [1], and the corollaries are the reduction of [4]. The alternation of Lemma 1 is [3, Algorithm 7, Lemma 41, Cor. 45], and [2, Section 2.3] names it as earlier work, the interwoven Dijkstra and Bellman-Ford. The merging of calls is [3, Cor. 27]. We add their use across all clusters at once through offsets, a self-contained form of the scaling with its behaviour on negative cycles, the certified negative side of Proposition 7, and three repairs, listed in Section 8. To our knowledge there is no earlier statement of Theorem 1 or 2 with Õ(D) rounds. Such a statement needs an exact Õ(D) oracle for nonnegative weights, which earlier work did not have.

## 2. Tools

Write w_φ(u, v) = w(u, v) + φ(u) − φ(v). For a set of arcs, dist(V, v) is the least weight of a walk ending in v, the empty walk included. Let G≥0 be G with weights max(w, 0).

**(O), the oracle.** Given nonnegative integer weights of polynomial size on the arcs of a digraph on G, and integer offsets x ≥ 0 on a set S of vertices, every vertex learns min_{u ∈ S} (x(u) + dist(u, v)) in Õ(D) rounds. This is the algorithm Exact of [1, Algorithm 1], which runs on any new weights. To remove an arc, give it a weight above every value that matters. Vertices compute new weights from their own potentials with one round of exchange. It runs on the reversed arcs as well, and on the face-disjoint graph Ĝ of [1].

**(M), minor aggregation.** A step of the Distributed Minor-Aggregation Model takes Õ(D) rounds on planar networks [5, Cor. 4.6, Lemma 4.8].

**Lemma 2 (decomposition) [3, Lemma 4, Cor. 27; Lemma 5, Prop. 32, Cor. 33].** Given nonnegative integer weights of polynomial size and an integer d ≥ 1, every vertex gets an integer index idx(v) of polynomial size, such that:

- vertices with equal index form a *cluster*, and with high probability any two u, v in a cluster have dist(u, v) ≤ d and dist(v, u) ≤ d in the whole graph with these weights;
- an arc is *cut* if it goes from a larger index to a smaller one, and it is cut with probability at most Q·w(e)/d + O(n^{−8}), with Q = O(log² n).

As stated in [3], the first bullet is false. This is the form with the repair of Section 8.

This takes Õ(1) calls of (O) and Õ(1) steps of (M). With E^rem = ∅ the same indices give the strong components in topological order, in O(log² n) calls of (O).

The set E^rem of [3, Lemma 4] is the set of removed arcs, and the clusters are the strong components without it, in the order of [3, Prop. 32], whose labels decrease along arcs, so idx is a constant minus the label, once the labels are repaired as in Section 8. A cut arc lies in E^rem. In [3, Cor. 27], recursive calls on vertex-disjoint sets are merged into one call of (O), by a large weight on the arcs between the sets.

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

At level L no arc is cut, so B(L) is the claim. On restricted input, potentials are bounded by n + n·max idx. There are L·R decompositions, and L·R·|Φ|·(t + 1) calls for Lemma 1. ∎

## 5. Scaling

Let w be integer weights of polynomial size, and x = 2((n + 1)w + 1). Then x(C) ≥ 2|C| for every cycle if w has no negative cycle, and x(C) < 0 for a simple cycle with w(C) < 0. The factor 2 in x is not essential. It is kept as in [2] and costs nothing.

**Lemma 5 (scaling).** Let x_φ ≥ −B with an integer B ≥ 1. Choose (ρ, α) = (⌈B/3⌉, 2) if B ≥ 5, (2, 1) if B is 3 or 4, (1, 1) if B = 2, and (1, 0) if B = 1. Let r = ⌊x_φ/ρ⌋ + α. If w has no negative cycle, then r has weights at least −1 and every cycle has r(C) ≥ |C|. If potentials ψ have r_ψ ≥ 0, then x_{φ+ρψ} ≥ −ρα. The value ρα is less than B in every case, so O(log nW) phases reach x_φ ≥ 0.

*Proof.* The floor of x_φ/ρ is at least −⌈B/ρ⌉, which is at least −(α + 1) in each case. For a cycle, ⌊y⌋ > y − 1 gives r(C) > x(C)/ρ + (α − 1)|C|. With α = 2, x(C) ≥ 0 suffices. With (2, 1), x(C)/2 ≥ |C|. With ρ = 1 the floor is exact, and r(C) = x(C) + α|C| ≥ 2|C|. Further, x_φ ≥ ρ⌊x_φ/ρ⌋ = ρ(r − α) ≥ ρ(ψ(v) − ψ(u) − α), which is the second claim. Finally 2⌈B/3⌉ < B for B ≥ 5. ∎

Arcs with r > n are dropped before Proposition 4 is applied, which keeps a restricted graph. The vertices check r_ψ ≥ 0 on the kept arcs first, since a negative cycle would otherwise feed (O) negative weights. One more call of (O) then gives dist(V, ·) in the graph without the dropped arcs. It is also dist(V, ·) for all arcs of r: a path with an arc above n has weight above n − (n − 1) > 0, and the empty path has weight 0. So this distance is a potential for all arcs of r. This is the note at the end of [2, Lemma 2.9].

*Negative cycles.* After each phase, the vertices check r_ψ ≥ 0 locally and aggregate the result in O(D) rounds. Values stay polynomial on every input, including inputs with a negative cycle: −(n − 1) − tn ≤ d_φ ≤ 0, since a walk is a simple path plus cycles and each negative cycle has an arc negative in w_φ. If w has no negative cycle, all checks pass with high probability. If w has a negative cycle, then x has one, and no potentials exist for x, so some check fails. A failed check is reported as a negative cycle.

*Distances.* With x_φ ≥ 0, one call of (O) from s gives dist_x(s, v). For a walk, x(P) = 2(n + 1)w(P) + 2|P|. A least walk in x is simple and has least w among walks, and has at most n − 1 arcs. So dist(s, v) = ⌊dist_x(s, v)/(2(n + 1))⌋. The arcs tight in x form a shortest-path tree, since all cycles of x are positive. With offsets −φ on all vertices, shifted by a constant, the same call gives dist_x(V, ·), and floor division by 2(n + 1) turns it into dist_w(V, ·), which is a potential for w. Offsets 0 do not give this: on n = 2 with the arc (0, 1) of weight −1, the true value at vertex 1 is −1.

*Proof of Theorem 1.* O(log n) phases, each with Õ(1) calls of (O) and steps of (M), and each call takes Õ(D) rounds. ∎

## 6. Flow and the corollaries

*Corollary 3.* As in the proof of the Dual SSSP Corollary of [1]: run Theorem 1 on Ĝ with the lengths of its Dual Distance Lemma. Ĝ is planar with at most 7n nodes and hop diameter at most 3D + 2, and an r-round algorithm on it runs in 2r rounds on G. ∎

*Theorem 2.* As in the proof of the Maximum Flow Theorem of [1], with the reduction of [4]: binary search on β between 0 and the capacity out of s, with a negative-cycle test by Corollary 3 in the dual with lengths c_β, O(log nU) tests. The range matters on parallel edges, where the maximum flow can exceed nU: 10 parallel arcs s→a and 10 parallel arcs a→t with U = 1 and n = 3 have flow 10, above nU = 3. A smaller range would make the rerun below loop for ever. For the largest feasible β, the distances ψ give the flow ψ(lft d) − ψ(rgt d) + β[d ∈ P] − β[rev d ∈ P]. It is feasible by construction, if the distances are right. Then one call of (O), with weight 0 on residual arcs, gives the set reached from s in the residual network. If the checks of Proposition 7 pass, this set is a cut with the value of the flow, and the output is right. Otherwise a test was wrong, which has probability at most n^{−c}, and the algorithm runs again. ∎

*Corollary 4.* This is [4]. Route b on a breadth-first tree: each tree edge gets the sum of b below it, in O(D) rounds, which gives a flow f_0 with net outflow b. A flow f with net outflow b is f_0 + g for a circulation g, and g(d) = ψ(lft d) − ψ(rgt d) for face potentials ψ. The condition f ≤ c is ψ(lft d) − ψ(rgt d) ≤ c(d) − f_0(d). This system of difference constraints has a solution if and only if the dual with lengths c − f_0 has no negative cycle. A dual 2-cycle d*, (rev d)* is negative exactly when c(d) + c(rev d) < 0, which excludes a flow directly. Use Corollary 3. ∎

*Corollary 5.* Corollary 4 needs demands with sum 0, so each case first tests the sum by one aggregation and reports that none exists if it is not 0. This test is needed. On the path a−b−c with X = {a, c}, Y = {b} and g = 1 the sum of b is 1, the dual has no negative cycle, and without the test the output is the dart c→b with a unmatched, a false perfect matching. The orientation of one edge with a = (1, 1) fails in the same way. Color the sides X and Y from a breadth-first tree, in O(D) rounds. For prescribed degrees g, set b = g on X and b = −g on Y, c(d) = 1 for darts from X to Y and c(d) = 0 for their reverses. An integer flow is the subgraph of the darts with f(d) = 1. The flow of Corollary 4 is an integer, since ψ is one. For perfect matching g = 1.

For out-degrees a(v), start from any orientation O_0. Reversing an arc from u to v moves one unit of out-degree from u to v. So set c(d) = 1 for the darts of O_0, c(d) = 0 for their reverses, and b(v) = outdeg_{O_0}(v) − a(v). The arcs to reverse are those with f(d) = 1. ∎

*Corollary 6.* The weights q·w − p have a negative cycle if and only if the minimum mean is below p/q. Two different means with cycle lengths at most n differ by at least 1/n². So O(log nW) tests with Theorem 1 find an interval of width below 1/n², which holds one fraction with denominator at most n. With W above every weight, one test at W + 1 tells whether there is a cycle at all. ∎

**Proposition 7 (certificates).** Each of these takes local checks and O(D) rounds of aggregation, and each is sound whatever (O), the decomposition and the tests returned.

(a) *Distances.* Let φ satisfy x_φ ≥ 0 and let D(v) be finite or ∞. Check that D(s) = 0, that D(v) ≤ D(u) + x_φ(u, v) on every arc with D(u) finite, that no arc goes from a finite to an infinite value, and that each finite v ≠ s has an in-arc from a finite vertex with equality. Then D = dist_{x_φ}(s, ·).

(b) *Flow.* Let f be antisymmetric with f ≤ c and conservation, of value λ, and let X be a set with s ∈ X and t ∉ X such that every dart leaving X has f = c. Then f is a maximum flow and X is a minimum cut.

(c) *Negative cycle.* Let p < 0 and q > 0 be integers, ψ integer potentials, X ≠ ∅ a set of vertices, and let each vertex of X point to an out-neighbour in X along an arc with q·w(u, v) − p + ψ(u) − ψ(v) = 0. Then G has a cycle of mean p/q.

*Proof.* (a) By induction, D(v) ≤ x_φ(P) for every walk P from s, and the third check means that unreached vertices are exactly those with ∞. Walk back from v along arcs with equality. A repeated vertex would give a simple cycle with x(C) = x_φ(C) = 0. But x(C) = 2(n + 1)w(C) + 2|C|, and 0 < 2|C| < 2(n + 1), so x(C) ≠ 0. So the walk ends in s, and D(v) is the value of a walk. (b) This is the max-flow min-cut argument: the value is the capacity of X. (c) Pointers on a finite set close into a cycle C. Summing the equalities around C gives q·w(C) = p|C|. ∎

Such a certificate exists when G has a negative cycle. Take the minimum mean p/q < 0 by Corollary 6 and potentials ψ for q·w − p by Theorem 1. A cycle of minimum mean has reduced weight 0, and all reduced weights are nonnegative, so all its arcs are tight. A nontrivial strong component of the tight arcs, by Lemma 2 with E^rem = ∅, gives X and the pointers. So Theorem 1 becomes Las Vegas: run again until a certificate passes. Corollaries 4 to 6 get certified answers in the same way, since a negative cycle in the dual excludes a flow, and potentials with a tight cycle prove the minimum mean.

## 7. Costs

With the Q of [3], t = O(log² n), R = O(log n), L = O(log n): Lemma 1 runs L·R·|Φ| = O(log³ n) times with t + 1 calls each, so O(log⁵ n) calls per restricted problem, plus O(log² n) decompositions. With O(log n) phases of scaling this is O(log⁶ n) calls of (O) and more for the decompositions, and O(log n) more for the binary search of Theorem 2. These are large factors. Only their polylogarithmic form is claimed.

## 8. Points in [3] and [2]

All have short repairs, and the proof above contains them. The first one matters.

- **[3, Cor. 33] is false as stated.** Section 5.2 of [3] recurses into connected components, and all components of one set inherit the same ℓ. The base case draws a label from [ℓN², (ℓ + n − 1)N²], which is one point when n = 1, while its correctness line claims an interval of length at least |V|². So equal labels do not mean one strong component, even with probability 1. With kept arcs a→b and c→d, N = 4 and a removed arc a→c of weight above d, the labels are (16, 0, 16, 0) for a, b, c, d on every run. On a 144-vertex grid with 30% of the edges kept as arcs, the expected number of colliding pairs is 156 to 2,812, depending on the reading. If the recursion runs on components of G minus E^rem, a removed arc can then lie inside a "cluster", which loses the hypothesis of Lemma 3, so the proof of Proposition 4 does not cover that step. Take n = 9 and three clusters x→y→z with weights −1, −1 and return z→x of 5, joined by arcs of weight 1. Each has weak diameter 5. If they collide, the shortest path in their union has 8 arcs against d = 5. No test gave a wrong output because of this, so it is a gap in the proof and not an observed failure. *Repair:* in the base case take r = ℓ·K + id(leader), with K above every identifier. [3] already elects this leader. Labels are then distinct with no randomness, and the order does not change, since ordered sets differ in ℓ. Recursion on components of the network also works, since no arc lies between colliding parts, although the first bullet of Lemma 2 stays literally false. Longer intervals of N^{c+2} values are a third way.
- [3, Cor. 27] asks for a threshold with exactly ⌈c log n⌉ vertices, which does not exist when V_i is smaller. Take all of V_i. [3, Cor. 33], line 1, draws numbers that are distinct with high probability in n_i only. Break ties by identifier.
- [2, Lemma 2.6] builds t + 1 layers where each crossing uses an arc, and it asks for the layer t. A path with fewer than t arcs does not reach this layer. The layered graph also is not planar, so we could not use it here in any case. Stay arcs of weight M repair it, and Lemma 1 does not need them.
- [2, Lemma 3.2] takes the return path Q in G[S], while the weak diameter holds in the whole graph. Lemma 3 above takes Q in the whole graph. The closed walk is still in the restricted graph. The conclusion of [2, Lemma 3.2] did not fail in any test.

## 9. Checks

`sim/negative/neg.py` runs all of the above centrally, with Dijkstra as the oracle and its own variant of Algorithms 1 and 2 of [3], which piles the geometric tail of [3, Definition 21] on the cap. Algorithm 3 of [3] is not implemented: the strong components and their order are computed directly, so this code cannot see the failure of [3, Cor. 33]. The truth is Bellman-Ford, Karp's theorem, and `networkx` for flow, matching and degrees. Each row below was run on the code that this note describes.

No `FAIL` in any counter. The last number of each command is its time in seconds.

| Lane | What it runs | Runs | Compared with the truth | Max n | Other |
|---|---|---|---|---|---|
| `neg.py 1001 300`, `2001 300` | Proposition 4 with R = 3, t = 8 | 1,528 | 1,603,955 values of A(ℓ), 2,936,330 arcs of B(ℓ), no miss | 100 | 46,246 decompositions, 128 gave up, largest t needed 2 |
| `neg.py 1002 900 big` | same | 392 | 2,480,672 values, 4,624,731 arcs, no miss | 625 | 15,683 decompositions, 24 gave up, shortest paths up to 575 arcs, largest t needed 3, up to 271,079 oracle calls in a run |
| `neg.py scale 1003 300` | Lemma 5, with Bellman-Ford as the restricted solver | 155,945 | 2,615,081 distances, 29,921 instances with a negative cycle; a false report counts as a `FAIL` | | 3,169,748 phases, B up to 38,563,838 |
| `neg.py full 1004 900` | Theorem 1, the whole stack | 130 | 2,112 distances, 36 instances with a negative cycle; a false report counts as a `FAIL` | 49 | up to 1,077,679 oracle calls in a run |
| `neg.py flow 3005 420` | Theorem 2 with its cut and rerun, and Corollary 5, in the dual | 283 flows, 195 matchings, 195 degree tests, 283 out-degree tests | value against `networkx`; flow checks and cut value on all 283; matching against Hopcroft-Karp; degrees and out-degrees against `networkx` | | 57 flows and 52 matchings with their degree tests on the whole stack, the rest with Bellman-Ford as the test; 75 flows with tests that lie, 28 reruns; 181 instances have a perfect matching, 110 and 176 degree and out-degree targets are feasible |
| `neg.py cert 3006 420` | Proposition 7 and Corollary 6 | 162 | mean against Karp's theorem; 141 cycle certificates give a real cycle of that mean; no potentials just above the mean and no tight cycle just below it; 131 distance certificates accepted; 480 corrupted answers all rejected | 40 | 8 runs on the whole stack, n ≤ 16; 31 with a negative minimum mean, 21 acyclic; 2,723 tests |

Every instance of Theorem 1 and Proposition 4 passes `nx.check_planarity`, and so does every flow and matching instance.

*The deterministic part of Proposition 4.* If at some level the success event fails, the proof says nothing, and otherwise it says that A(ℓ) and B(ℓ) are exact. With t and R far below the theory the event fails often, so this is testable, `neg.py event <seed> 300 <t> <R>`. A step counts as inexact if it misses in A or B.

| t, R | Runs | Event holds | Event fails | Runs with an inexact step | Wrong output | Inexact although the event holds |
|---|---|---|---|---|---|---|
| 2, 2 | 215 | 212 | 3 | 3 | 0 | 0 |
| 2, 1 | 423 | 382 | 41 | 41 | 1 | 0 |

In these runs the inexact steps and the failures of the event coincide exactly. Cut arcs are almost always negative in w_φ and `needed_t` already minimises over shortest paths and repetitions, so this is close to a restatement.

*Negative controls.* `neg.py ctl <seed> 40 [t]`, with R = 2. The rows share one sequence of instances, except `oneR`, which draws differently after its first instance. A control counts a wrong final potential.

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
- Lemma 2 is a black box from [3]. We read its algorithms and its proof in CONGEST. `neg.py` implements a variant with the constant c = 1, far from the "sufficiently large" of its proof. So the probability bound with its constants is untested. The code reports how often the decomposition gives up and how many cut arcs a path has.
- The parameters are not a stress test. The simulation uses t = 8, R = 3 and c = 1, not the values of the theorem, and small c means fewer cuts. With no negative cycle and n ≤ 9, a shortest path has at most 8 arcs, so t = 8 is exact on those lanes whatever the decomposition does. On a hub-rim family the needed t reaches 13 with R = 1 and 9 with R = 3, both at c = 4, the latter at n = 1,025, where the event for t = 8, R = 3 fails. Outputs stayed right at n ≤ 151, below that point. "Largest t needed 3" in the table is specific to the family and to c = 1.
- `neg.py` works in the dual directly, not through Ĝ.
- The whole stack on Corollaries 4 to 6 is small: see the counts in the table.
- `neg.py` has no instances with parallel edges. The range of β in Theorem 2 is by hand.
- The source behind [2, Lemma 2.9], used in Section 5, is not checked.
- The Lean file covers the arithmetic only: Lemma 5 for B ≥ 5 and its cycle bound, an upper bound of Lemma 1 for a given alternation, the arithmetic of Lemma 3 given the closed-walk inequality, and the arc inequality of Proposition 4. It has no graphs, and no probabilities, Lemma 2, flow, Proposition 7 or simplicity of least walks.

## References

1. S. Senge. Exact Shortest Paths and Maximum Flow in Planar Networks in the CONGEST Model. This repository, tag `arxiv-v1`.
2. N. Fischer, B. Haeupler, R. Latypov, A. Roeyskoe, A. L. Sulser. A Simple Parallel Algorithm with Near-Linear Work for Negative-Weight Single-Source Shortest Paths. SOSA 2025, 216-225, arXiv:2410.20959.
3. V. Ashvinkumar, A. Bernstein, N. Cao, C. Grunau, B. Haeupler, Y. Jiang, D. Nanongkai, H. H. Su. Parallel, Distributed, and Quantum Exact Single-Source Shortest Paths with Negative Edge Weights. ESA 2024, arXiv:2303.00811.
4. G. L. Miller, J. Naor. Flow in planar graphs with multiple sources and sinks. SIAM J. Comput. 24(5), 1995.
5. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
6. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in Undirected Planar Graphs. DISC 2026, arXiv:2608.09500.
