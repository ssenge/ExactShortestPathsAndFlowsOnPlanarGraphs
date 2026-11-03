# Replacement paths on planar digraphs

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/replacement/`, elementary core in `lean/SsspFlow/Replacement.lean`. No human has checked it. It rests on the Exact SSSP Theorem and the Label Hypothesis of [1]. Importance: modest. It gives bounds on planar networks for problems with near-linear lower bounds on general networks, and the proofs are short.

The model is CONGEST on a connected planar network G with n vertices and hop diameter D, with a known embedding. Õ hides factors polylogarithmic in n. A *digraph on G* has its arcs on edges of G.

## 1. Results

Let H be a digraph on G with integer weights of polynomial size, s and t vertices, and P a shortest s-t path with h arcs, whose vertices know their arcs of P. Let W be the weight of P. For an arc e of P, the *replacement distance* R(e) is the distance from s to t in H − e, and ∞ if there is no path.

**Theorem 1 (exact).** Let the weights be nonnegative. Given the Label Hypothesis, in Õ(D · min(h, D)) rounds the two ends of every arc e of P learn R(e).

**Theorem 2 (approximate).** Let the weights be nonnegative, and let 0 < ε ≤ 1 with 1/ε of polynomial size. Given the Label Hypothesis, in Õ(D/ε) rounds the two ends of every arc e of P learn R′(e) with

R(e) ≤ R′(e) ≤ W + (1 + ε)(R(e) − W).

So the error is relative to the excess over W, not to R(e). In particular R′(e) = W if R(e) = W, and R′(e) = ∞ if and only if R(e) = ∞.

**Theorem 3 (undirected).** Let H be undirected with positive weights. After two exact shortest-path trees, O(log² n) steps of (M) let the two ends of every edge e of P learn R(e). Given the Label Hypothesis this takes Õ(D) rounds.

**Corollary 4.** In the bounds of Theorems 1 and 3, all vertices learn the weight of a second simple shortest s-t path, the arcs of such a path are marked, and all vertices learn an arc of P that maximizes R (a *most vital arc*). In the bound of Theorem 2 the same holds with values of R′.

**Corollary 5.** Let the weights be positive. Given the Label Hypothesis, in Õ(D²) rounds the two ends of every arc of H learn the least weight of a cycle through that arc, and each vertex the least weight of a cycle through it. A (1 + ε)-approximation takes Õ(D/ε) rounds.

With negative weights and no negative cycle, potentials from `notes/NEGATIVE.md` reduce Theorems 1 and 2 to the nonnegative case, with high probability and Õ(D) more rounds.

A cycle of length 2D with s and t opposite gives Ω(D): R(e) on P depends on the weights of the other side. So Theorem 3 is optimal up to polylogarithmic factors. Whether Theorem 1 holds in Õ(D) is open.

**Context.** Bounds on general networks, with SSSP the round complexity of exact SSSP:

| Problem | General networks | Planar, here |
|---|---|---|
| Directed weighted, exact | Θ̃(n) [2] | Õ(D · min(h, D)) |
| Directed unweighted, exact | Θ̃(n^{2/3} + D) [3] | the same |
| Directed weighted, (1 + ε) | Õ(n^{2/3} + D) [3] | Õ(D/ε), on the excess |
| Undirected weighted, exact | O(SSSP + h), and Ω̃(√n + D) [2] | Õ(D) |
| Undirected unweighted, exact | Θ(D) [2] | nothing new |
| Least cycle through each vertex, directed | Θ̃(n) [2] | Õ(D²) |

To our knowledge there is no earlier bound for replacement paths on planar networks. The minimum over all arcs in Corollary 5 is the directed girth. [4] has the directed global minimum cut in Õ(D²) rounds, which is that problem on the dual.

**What is new.** Little. Lemma 1 is the residual graph, used for a pair of paths in [5], and we do not claim it as new. Lemma 3 is the formula of [6] for undirected graphs, and Theorem 3 replaces the term h in [2] by Õ(D) with (M). Lemma 2 is a small observation on the bags of [1]. The contribution is that these parts with the oracle of [1] give the first two rows of the table.

## 2. Tools

**(O), the oracle.** As in `notes/NEGATIVE.md`, Section 2. Given nonnegative integer weights of polynomial size on arcs on G, and offsets on a set S, every vertex learns its least value of offset plus distance from S, in Õ(D) rounds. This is the algorithm Exact of [1, Algorithm 1]. An arc is removed by a weight above all that matters. The reversed digraph is a digraph on G as well.

**(M), minor aggregation.** A step of the Distributed Minor-Aggregation Model takes Õ(D) rounds on planar networks [4, Cor. 4.6, Lemma 4.8]. It covers aggregates over connected parts.

**Bags.** A bag hierarchy of [1, Section 3.1] is a rooted tree of bags X, each with a vertex set, a set A_X of arcs with both ends in X, and a set H_X ⊆ X of hubs, such that (V1) the root holds all vertices and arcs, (V2) every vertex of X ∖ H_X lies in exactly one child of X, and (V3) every arc of A_X with both ends in X ∖ H_X lies in A_Y for some child Y. The *chain* of v starts at the root and follows the child that holds v, until the first bag in which v is a hub. The Label Hypothesis gives a hierarchy of height O(log n) with |H_X| = Õ(D) for non-leaf bags, Õ(D) vertices in a leaf, a tree T_X of diameter Õ(D) that spans X, at most two trees of one depth on each edge, and known chains. It also gives the labels (L2), which approximate distances to and from hubs.

## 3. The residual digraph

Take φ(v) = dist(s, v), from one call of (O), and drop the vertices that s does not reach. The *reduced weight* of an arc (x, y) is w̃(x, y) = w(x, y) + φ(x) − φ(y) ≥ 0, and it is 0 on P. Let H′ be H with the arcs of P removed, and with the reverse of each arc of P added with reduced weight 0. Parallel copies of an arc of P stay. Let d′ be distance in H′ under reduced weights. All of this is known locally after one round.

**Lemma 1.** For an arc e = (v_i, v_{i+1}) of P, with P = v_0, …, v_h, we have R(e) = W + d′(v_i, v_{i+1}).

*Proof.* (≤) Take a walk π from v_i to v_{i+1} in H′, and call the index on P of a vertex of P its position. Let v_a be the last vertex of π with position at most i, and v_b the next vertex of P on π. Then b > i. Reversed arcs lower the position, so the piece of π from v_a to v_b consists of arcs of H that are not on P. So P up to v_a, this piece, and P from v_b form an s-t walk in H − e. Its reduced weight is that of the piece, at most that of π, and reduced weights along an s-t walk add up to its weight minus W.

(≥) Take an s-t path Z in H − e. Let v_a be its last vertex of position at most i, and v_b the next vertex of P on it, so b > i. The piece of Z from v_a to v_b avoids the arcs of P: a single arc of P from position at most i to one above i is e. So the piece is in H′. In H′, the reversed arcs lead from v_i to v_a and from v_b to v_{i+1} at cost 0. So d′(v_i, v_{i+1}) is at most the reduced weight of the piece, which is at most that of Z, namely w(Z) − W. ∎

So all replacement distances are distances between the ends of arcs in one digraph on G. For small h this ends the proof of Theorem 1: one call of (O) from v_i for each arc gives R(e), in Õ(h · D) rounds.

## 4. Exact labels

Let X′ be the set of vertices with X on their chain, let A′_X be the arcs of G with both ends in X′, and let H′_X be the set of vertices whose chain ends in X.

**Lemma 2.** (a) These sets form a bag hierarchy, and the bags of one depth are vertex-disjoint. (b) For any digraph on G with nonnegative weights, in Õ(D²) rounds every vertex v learns, for each X on its chain and each h in H′_X, the distances from v to h and from h to v in (X′, A′_X). (c) For any vertices x, y, the distance from x to y is the least sum of these two values over bags X on both chains and h in H′_X.

*Proof.* (a) A vertex has one bag per depth on its chain, so the bags of a depth are disjoint. For (V3), we show by induction that an arc with both ends in X′ lies in A_X. It holds at the root. If X has parent Z, both ends are in Z′ and not hubs of Z, so the arc is in A_Z by induction, and by (V3) it is in A_Y for a child Y of Z that holds both ends. By (V2) this Y is X. So (V3) for the original bags gives (V3) for the new ones. (V1) and (V2) are immediate, and a hub of X is a hub of the new bag exactly if its chain reaches X, which is the definition of H′_X.

(b) Each vertex knows its chain, and neighbours exchange chains, so each vertex knows which of its arcs lie in which A′_X. A convergecast and broadcast over T_X, pipelined, numbers H′_X in each bag, in Õ(D) rounds per depth. For each depth and each number k, make one call of (O) in each direction on the union of the A′_X of that depth, with offset 0 on hub k of each bag. By (a) no arc joins two bags of the depth, so each vertex gets the distance from the hub of its own bag. There are O(log n) depths and Õ(D) numbers, which gives Õ(D) calls. Only the hierarchy is taken from the hypothesis, once, for example with unit lengths, and it depends on no weights.

(c) The sum is the length of a walk from x to y, so it is at least the distance. For the other direction, take a shortest path, and the proof of the Virtual Source Lemma [1] on the hierarchy of (a) with exact values: walk down from the root as long as the path has no hub of the current bag. All of the path then lies in one child, by (V2) and (V3). This ends at a bag X with a hub h on the path, and all of the path lies in (X′, A′_X). ∎

*Proof of Theorem 1.* Build the labels of Lemma 2 for H′, or use the h calls of Section 3 if h ≤ D. Each label has Õ(D) words. The two ends of an arc of P exchange theirs in Õ(D) rounds, and each vertex has at most two arcs of P. By Lemma 2(c) and Lemma 1 they compute R(e). ∎

## 5. The approximate form

*Proof of Theorem 2.* The Label Hypothesis asks for lengths in [1, W′] and for arcs both ways on each edge. Let K be an integer of at least 4n/ε, give each arc of H′ the length ℓ = K w̃ + 1, and give each absent arc a length B greater than (1 + ε/2)(K n max w̃ + n). All are of polynomial size. For x and y in H′ with d′(x, y) finite, the distance under ℓ lies between K d′ and K d′ + n, and if d′ is infinite, it is at least B.

Run the hypothesis for H′ with ε/2. The ends of an arc of P exchange their labels and the distances in their common leaf, which they know as in [1, Corollary to the Virtual Source Lemma]. Let d̃ be the least sum, over common bags and hubs. Apply the Virtual Source Lemma of [1] with offset 0 at v_i and no other offset: then d̃ lies between the distance under ℓ and 1 + ε/2 times that distance.

If d̃ ≥ B, report ∞. Otherwise let R′(e) = W + ⌊d̃/K⌋. Then ⌊d̃/K⌋ ≥ d′, and

⌊d̃/K⌋ ≤ (1 + ε/2)(d′ + ε/4).

If d′ = 0, the right side is below 1, so the value is 0. If d′ ≥ 1, it is at most (1 + ε/2)(1 + ε/4) d′ ≤ (1 + ε) d′. With Lemma 1 this is the claim. ∎

## 6. Undirected networks

Let H be undirected with positive weights, and let T be a shortest-path tree from s that contains P. For a vertex u, let α(u) be the index of the last vertex of P on the path of T to u. So the sets {u : α(u) = a} are the trees that hang from v_a, which are connected and disjoint. Let d_s and d_t be the distances from s and to t.

**Lemma 3 ([6]).** For an edge e_i = {v_i, v_{i+1}} of P,

R(e_i) = min { d_s(u) + w + d_t(v) : {u, v} an edge not on P with weight w, α(u) ≤ i < α(v) }.

*Proof.* Every s-t walk in H − e_i goes from {α ≤ i} to {α > i} over an edge not on P, and its parts before and after that edge weigh at least d_s(u) and d_t(v). So R is at least the minimum. For the other direction, the path of T to u avoids e_i, since α(u) ≤ i. It is enough that no shortest path from v to t uses e_i when α(v) > i. The path of T to v runs through v_i, then v_{i+1}, so d(v_i, v) = w_i + d(v_{i+1}, v), with w_i the weight of e_i. A path from v through v_i and then over e_i to v_{i+1} would weigh d(v, v_{i+1}) + 2 w_i + d(v_{i+1}, t), more than a path through v_{i+1} directly. A path from v that goes over e_i from v_{i+1} to v_i would give d(v_{i+1}, t) = w_i + d(v_i, t), while P gives d(v_i, t) = w_i + d(v_{i+1}, t), which contradicts w_i > 0. ∎

Positive weights are needed: with zero weights the simulation's control `zero` fails.

*Proof of Theorem 3.* Two trees from s and t give d_s, d_t and T. Vertices of P take the arcs of P as tree arcs, which are tight. Positions on P come from prefix sums in (M), and one aggregate over each hanging tree gives α. Each edge {u, v} not on P with α(u) < α(v) then stands for an interval [α(u), α(v)) of arcs of P with a value, and by Lemma 3 we want, for each arc, the least value of the intervals that hold it.

For an interval [a, b), let t be the highest bit in which a and b differ. They agree above t, and a has 0 and b has 1 at bit t. So at level t, the positions that agree above t form a block, a lies in its lower half and b in its upper half. For each level, an aggregate over each hanging tree gives X_t(a), the least value of the intervals of level t that start in the tree of v_a, and Y_t(b) likewise for those that end in the tree of v_b. For i in the lower half of a block, the level gives the minimum of X_t(a) over a ≤ i in that half, and for i in the upper half, the minimum of Y_t(b) over b > i in that half. These are prefix minima on disjoint subpaths of P. A prefix minimum takes O(log n) steps of (M): recursively, each subpath finds the minimum of its first half and tells its second half. This gives O(log² n) steps in all. ∎

## 7. The corollaries

*Corollary 4.* A simple s-t path other than P misses an arc of P, so the second path has weight min R(e). One aggregate over P gives this minimum and the maximum of R. To mark the path on digraphs, make one call of (O) from v_i in H′, with lengths K₀ w̃ + 1 and K₀ = n + 1 so that tight arcs form a forest, and mark the forest path to v_{i+1} by a subtree sum. As in Lemma 1, the piece of it from the last vertex of position at most i to the next vertex of P has no inner vertex on P, and is found by aggregates over the marked path. With P it gives a simple path. On undirected networks, the edge {u, v} of Lemma 3 with the two tree paths gives it, and a walk of least weight is simple since weights are positive. ∎

*Corollary 5.* Use the labels of Lemma 2 for H, or those of the hypothesis as in Section 5 for the approximation. Each edge of G carries its two ends' labels in Õ(D) rounds, so an arc (x, y) learns w(x, y) + d(y, x). A shortest path from y to x visits x only at its end, so it does not use (x, y), and arc and path form a simple cycle. A vertex takes the minimum over its in-arcs. ∎

## 8. Checks

`sim/replacement/rp.py` computes the values centrally, with Dijkstra as the oracle. The truth is one further Dijkstra with the arc removed, or Bellman-Ford with negative weights, for each arc of P. Every instance passes `nx.check_planarity`. The families are grids with diagonals, wheels, cylinders and contracted grids, and the last give high degree at low diameter. The bags of the simulation are components after removing a random BFS layer, so their hubs are not those of [1]. The labels are computed by the calls of Lemma 2, one source per bag. The labels of Theorem 2 are the exact ones, each multiplied by a random factor up to 1 + ε/2, which is noise and not an optimized worst case.

| Check | Main lane | Big lane | Failures |
|---|---|---|---|
| Lemma 1, arcs of P | 435,819 | 232,511 | 0 |
| Lemma 2(c), the same arcs | 435,819 | 232,511 | 0 |
| Lemma 2(c), random pairs | 950,535 | 389,466 | 0 |
| Theorem 2, arcs of P | 435,819 | 232,511 | 0 |
| Corollary 4, second path | 174,085 | 74,756 | 0 |
| Corollary 5, arcs of H | 949,909 | 391,468 | 0 |
| Lemma 3 and the intervals, edges of P | 401,022 | 211,623 | 0 |

The lanes ran 404,245 and 165,645 instances, with n up to 48 and 143, P of up to 23 arcs, and 4,883,646 oracle calls for the labels. A fifth of the digraph instances have negative weights, and about a third have zero weights.

Negative controls, each of which must fail:

| Control | What it breaks | Runs | Failures |
|---|---|---|---|
| `noreverse` | H′ without the reversed arcs | 437 | lemma1 463 |
| `keep` | H′ keeps the arcs of P | 10,766 | lemma1 21,081 |
| `lowest` | query in the lowest common bag only | 5,627 | labels 1,960, pairs 2,540 |
| `leak` | bags keep the hubs of the parent, so one call mixes sources | 6,165 | labels 1,298, pairs 937 |
| `smallK` | K = 1 in Theorem 2 | 7,877 | approx 7,866 |
| `asym` | Lemma 3 on asymmetric weights | 89,190 | un 57,581 |
| `inclusive` | intervals [a, b] in place of [a, b) | 98,014 | un 21,969 |
| `zero` | Lemma 3 with zero weights | 34,281 | un 7,608 |

## 9. Not covered by the checks

- Rounds and messages: there is no CONGEST simulation, and the number of calls in the simulation says nothing about Õ(D), since its hubs are not bounded by D.
- The Exact SSSP Theorem, the Label Hypothesis and their caveats in [1]. The steps of (M) as black boxes.
- The Lean file covers the crossing step of Lemma 1, the telescoping of reduced weights and the two cases of Lemma 3, not the graph statements or the rounds.
- The marking of a path in Corollary 4 by aggregates: the simulation cuts the path centrally.

## References

1. S. Senge. Exact shortest paths and flows on planar graphs in CONGEST. This repository, tag `arxiv-v1`.
2. V. Manoharan, V. Ramachandran. Near optimal bounds for replacement paths and related problems in the CONGEST model. arXiv:2205.14797, brief announcement at PODC 2022.
3. Y.-J. Chang, Y. Chen, D. Dey, G. Mishra, H. T. Nguyen, B. Sanchez. Optimal distributed replacement paths. arXiv:2502.15378.
4. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
5. J. W. Suurballe, R. E. Tarjan. A quick method for finding shortest pairs of disjoint paths. Networks 14(2), 1984.
6. J. Hershberger, S. Suri. Vickrey prices and shortest paths: what is an edge worth? FOCS 2001.
