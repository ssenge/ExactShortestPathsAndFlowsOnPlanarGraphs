# Exact eccentricities and diameter of unweighted planar networks in Õ(D²) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/diameter/`. It uses the region bags of `notes/LEMMA15.md`, Section 9, and the pattern bound of [2]. It does not use the labels (L2) of the Label Hypothesis of [3]; of that form it uses only the clauses (V1) to (V3) and (L1) of §9.9, and these have no black box beyond the given embedding.
Importance if it survives: solid, since the best stated bound for the diameter is Õ(D³) [2].

The model is CONGEST on a connected, undirected, unweighted planar network with n vertices and hop diameter D, with a known embedding. Õ hides
factors polylogarithmic in n. Words have O(log n) bits.

## 1. Result

**Eccentricity Theorem.** In Õ(D²) rounds every vertex learns its eccentricity. So the diameter, the radius and the centre are computed in Õ(D²)
rounds. Given the embedding, the algorithm is deterministic.

**Context.** The bounds for the exact diameter are Õ(D⁵) [1], randomized, Õ(D⁴) [4], and Õ(D³) by the pattern bound [2]; the last two are stated in [2], which does not discuss determinism, so determinism is an additional claim here. General algorithms with O(n) rounds exist, so Õ(D²) is new only for D well below √n.
Three things give the improvement.
- For one pattern only the largest offset matters. This observation is in [2, Section 3], citing [6, Corollary 9], and it removes a factor D.
- A segment tree over the face holds all patterns in Õ(D²) words. [2] reports a compression with Õ(k²) words from [4]; what is new is the distributed form, which rests on Lemma 3.
- Cutting the plane along a connected subgraph of real edges puts all hubs of a bag on one face, or several faces whose walks have Õ(D) total length.

To our knowledge there is no bound below Õ(D³).

## 2. What is used from the hierarchy

From `notes/LEMMA15.md`, Section 9 (Lemmas B1 and B5, and the round count there). T is a BFS tree of G with root r. A bag X has a region graph R_X, a
subgraph of G, with vertex set V(X), and R_root = G.

- (H1) The tree of bags has height O(log n). A non-leaf X has a path q_X of T_X, so of real edges, with at least one edge. S_X = V(q_X). A leaf has Õ(D) vertices.
- (H2) R_X has a spanning tree T_X of diameter Õ(D). For each depth, every edge of G lies in at most two graphs R_X. So the bags of one depth can run a
  pipelined broadcast or convergecast of w words, in parallel, in Õ(D + w) rounds.
- (H3) For a child Y of X, V(Y) ⊆ V(X) and R_Y ⊆ R_X. A vertex x ∉ S_X of V(X) lies in exactly one child Y of X, and every edge of R_X at x lies in R_Y. A path in R_X that avoids S_X lies in one
  child.
- (H4) All this is built in Õ(D) rounds, deterministically, and each vertex knows its chain and, for each of its edges, the bags that contain it.

The closing edges of the separators of Lemma B5, which may be virtual, are not used here.

Two parts of these statements are needed. Without V(Y) ⊆ V(X) in (H3), a planar instance with n = 7 satisfies the rest of (H1) to (H3) and gives E(2) = 3 against the true 2. Without q_X being a path of T_X in (H1), the length of q_X is not bounded by Õ(D): a wheel with q_root on the rim has D = 2 and Θ(n²) words.

The *chain* of v starts at the root and goes from X to the child that holds v as long as v ∉ S_X and X is no leaf. X° is the set of vertices with X on
their chain. For a parent A of X let Q_A be the union of S_B over B on the path from the root to A, with B = A included. Then X° = V(X) ∖ Q_A, and V(root)° = V. Indeed a chain stops at the first S_B it meets, and a vertex of V(X) off Q_A lies, by (H3), in the child towards X at each bag on that path.

**Fact 0 (first hub).** Let X be a non-leaf, let u ∈ X° and let Q_X be the union of S_A over A on the path from the root to X, with A = X included. Let π be a path in G from u whose
vertices before its last one avoid Q_X, with u ∉ Q_X. Then π lies in R_Y, for the child Y of X that holds u.

*Proof.* Go along the chain from the root to Y. Suppose that all vertices of π before its last one lie in A°, and that all edges of G at them lie in R_A, which is true at the root. These vertices are off S_A, so by (H3)
each lies in exactly one child of A, which holds all its edges. Consecutive ones share an edge, so they share the child, which is the next bag on the chain of u. So the claim holds for that child. At Y it says that all edges of π lie in R_Y. ∎

## 3. Cutting along P

For a bag X let P_X be the subgraph of G with the edges of q_A for all A on the path from the root to X, and for each such A the edges of the T-path
from the first vertex of q_A to r. Then P_X is **connected**, consists of real edges, contains Q_X, and has Õ(D) edges.

**Faces and corners.** Since P_X is connected, each face Φ of P_X is an open disc, bounded by a closed walk of length K_Φ, and Σ_Φ K_Φ = 2|E(P_X)|. The walk
passes one corner of P_X per step. A corner is an angle at a vertex x(o) between two edges of P_X that are consecutive around x(o); we call it an
*occurrence* o. A vertex off P_X lies in one face. An edge of G outside P_X at a vertex x of P_X lies in exactly one corner.

**The graph W_Φ.** Take a cycle with one vertex per occurrence on the walk of Φ, in the order of the walk. Add inside it the vertices of V(X) off P_X that lie in Φ, and the edges of R_X outside P_X that are drawn
in Φ, where an end at x ∈ P_X goes to the occurrence of its corner. This is a plane graph, undirected and unweighted, with the cycle as a face. It is connected: a path in T_X from a vertex in Φ to q_X reaches P_X at an occurrence of Φ. Mapping nodes to
their vertices of G maps every edge to an edge of G. So distances in W_Φ are at least the distances in G. For u off P_X in Φ let

    t_u(o) = dist in W_Φ from u to o.

**Lemma 1 (formula).** Let u, v ∈ X° be off P_X, in different children of X or in different faces of P_X. Then

    d_G(u,v) = min { d_G(u, x(o′)) + t_v(o′) : o′ on the face of v, x(o′) ∈ V(X) }.

*Proof.* Every term is at least d_G(u,v), by the mapping above. Let π be a shortest u-v path. It meets P_X: different faces are separated by P_X, and if π avoids
P_X then by Fact 0 it lies in the child of u, and v lies in exactly one child, so the children agree. Let b be the last vertex of π on P_X. The part from v to b has no vertex on Q_X before b, so
by Fact 0 it lies in R_X, and it has no edge of P_X, since its vertices before b are off P_X. So it is a path in W_Φ from v to the occurrence o′ of the corner that holds its last
edge, and b ∈ V(X). So t_v(o′) is at most its length, and the term at o′ is at most d_G(u,b) + d_G(b,v). ∎

The hypothesis on u and v is needed: on other pairs the formula can be too high. Hubs S_X alone are not enough below the root, since a shortest path may leave R_X. On region bags they give a wrong value on about 1% of pairs. This is why P_X holds all of Q_X.

**Lemma 2 (patterns).** The *pattern* of u on Φ is the vector of differences of t_u along the walk, and the *offset* is t_u at the first occurrence. The vectors of all u in
Φ have at most 2K² − 2K + 2 patterns, with K = K_Φ.

*Proof.* The proof of [2, Theorem 1], which gives this constant, applied to W_Φ and the face given by its cycle. For K = 2, P_X is one edge, and there is one difference in {−1,0,1}. ∎

The constant of Lemma 2 may not be tight. The largest counts found for K = 3, ..., 8, 10, 14 are 7, 13, 21, 31, 42, 55, 68, 76 patterns, which is K² − K + 1 for K ≤ 6.

**Lemma 3 (interval).** Let I be an arc of m consecutive differences on the walk of Φ. The restrictions of the patterns to I take at most (2m)² + 1 values.

*Proof.* For K = 2 there are at most 3 values. Let K ≥ 3. Subdivide all edges of W_Φ, as in [2]. For each u the differences along the cycle become a cyclic vector w_u ∈ {−1,+1}^{2K}, with sum 0, and I becomes n = 2m consecutive entries. The restriction of w_u to I
determines the restriction of the pattern. No two vectors have a *forbidden configuration* [2, Definition 1], that is, positions a, b, c, d in cyclic order at which w_u − w_v alternates in sign. Suppose they have one, positive at a, with entry i the step from cycle node i to node i + 1, and let g = t_u − t_v. Let s₁ be a maximum of g on the nodes a + 1, …, b, let s₂ be a minimum on b + 1, …, c, let s₃ be a maximum on c + 1, …, d, and let s₄ be a minimum on d + 1, …, a. Then g(s₁), g(s₃) > g(s₂), g(s₄). In the disc, shortest paths from v to s₁, s₃ and from u to s₂, s₄ must share a vertex, for some s_i with i odd and s_j with j even. Exchanging the parts after it gives g(s_j) ≥ g(s_i), a contradiction.

Let r_u be the number of +1 in w_u on I, and let w⁺_u be w_u on I followed by the block (+1)^{n−r_u} (−1)^{r_u}. It has length 2n and exactly n entries +1. Suppose w⁺_u and w⁺_v have a
forbidden configuration, read in the linear order. If r_u = r_v the blocks are equal, so it lies in I, which is excluded. So say r_u < r_v. Entries of the block differ only where u has +1 and v has −1, so all differences in the block have one sign. Two consecutive indices of the
configuration have opposite signs, so at most d lies in the block. If none does, the configuration lies in I, which is excluded. Otherwise a, b, c lie in I, and w_u − w_v is positive at d, so its signs on a, b, c are −, +, −.
Since r_u < r_v the sum of w_u − w_v over I is negative, and the sum over the whole cycle is 0, so w_u − w_v is positive at some entry p outside I. Then a, b, c, p are four positions in cyclic order with alternating signs, which is
excluded. By [2, Lemma 1], with length 2n and n entries +1, there are at most n·n + 1 vectors w⁺, and w⁺ determines the restriction. ∎

## 4. The algorithm

Depths run one after the other, top down, and bags of one depth in parallel by (H2). Let k = 2|E(P_X)| = Õ(D). For a leaf X let L_X = V(X), and otherwise L_X = V(P_X) ∩ V(X). Below, depth D in source detection means twice the height of T, which is known after one convergecast and lies between D and 2D; this changes no proof.

**Step 1: P_X.** Once, in O(D) rounds, every vertex learns its path in T to r, with the positions of its edges in the rotations, by pipelining from the root. The first vertex of q_X learns q_X with its rotation positions by one upcast over T_X, in Õ(D) rounds, adds this path to q_X and broadcasts
both over T_X, Õ(D) words. Vertices of X know P_A for the parent A from the earlier broadcast in A. Then every vertex of X computes the faces, walks and corners of P_X locally, and a vertex on P_X knows the corner of
each of its edges.

**Step 2: distances in G, on L_X.** Invariant: every v ∈ V(X) knows d_G(v,p) for all p ∈ L_X. In the root, run BFS from all of L_root in O(D + k) rounds by source detection [5]. Let X have parent A. Run source detection in R_X from all q ∈ L_X, to depth D, in Õ(D)
rounds, which gives values b_v(q). Each q ∈ L_X broadcasts its row d_G(q,p), p ∈ L_A, over T_X, in Õ(k²) words. So every vertex of X knows L_X, and from P_A it knows X° ∩ L_X, by X° = V(X) ∖ Q_A. Then

    d_G(v,q) = min( b_v(q), min_{p ∈ L_A} d_G(v,p) + d_G(p,q) ).

*Proof.* Each value is at least d_G(v,q). Let π be a shortest path. If it meets P_A, take the first such vertex p. It lies in L_A: either v ∈ P_A and p = v, or v ∈ A° and Fact 0 applies. Otherwise v, q are off P_A, so X is the only child of A that holds v, and
by Fact 0, π lies in R_X. It has at most D hops. ∎

**Step 3: t.** In a non-leaf, take the graph W′ with one node per occurrence o with x(o) ∈ V(X), one per vertex of V(X) off P_X, and the edges of R_X outside P_X; an occurrence is simulated by its vertex, and each edge of W′ is one edge of R_X. Run source detection [5] in W′ from all occurrences, to depth D + K_max, with K_max the largest K_Φ, in Õ(D) rounds.
This gives values f_a(o) for all nodes a of W′, with f_a(o) = ∞ beyond that depth. Occurrences broadcast their values over T_X, in Õ(k²) words. So every vertex of X knows the metric d″ on the occurrences of each face, given by the cycle and these values. Then, for u off P_X on Φ,

    t_u(o) = min_{o′} f_u(o′) + d″(o′,o).

*Proof.* W′ lies in the union of the W_Φ, so the right side is at least t_u(o), and d″ is at least the distance in W_Φ. Conversely a shortest path in W_Φ from u to o has length at most D + K_Φ: a shortest G-path from u to S_X has at most D hops, and its part up to the first vertex of P_X lies in W_Φ by Fact 0, which gives an occurrence at distance at most D, and every other one is at most K_Φ further on the cycle. Up to its first occurrence o′ it lies in W′, and so does each stretch between two consecutive occurrences that does not use the cycle. So this path gives the same value. ∎

**Step 4: dictionary.** On the positions of each walk fix a segment tree, by halving. A leaf of the tree is one difference, in {−1,0,1}. Going up level by level, a vertex u ∈ X° off P_X forms for its node I the pair of identifiers of its restrictions to the two children of I. All pairs of one level of the tree are sent up T_X by a filtered upcast, duplicates removed. The root of T_X numbers them and broadcasts them. By Lemma 3, nodes with m differences hold at most 4m² + 1 pairs, so a walk of length K costs Σ_m (K/m)(4m² + 1) = O(K²) words over all levels, where m runs over powers of 2 up to K, and Σ_Φ K_Φ² ≤ k². This takes Õ(D²) rounds. Every vertex of X then knows the whole dictionary, and every u knows the identifier of its pattern.

**Step 5: tokens.** For each face and pattern, compute by a convergecast over T_X the largest offset, the child of a vertex that attains it, and the largest offset among vertices in another child. The keys are known from the dictionary, so this is one pipelined convergecast with O(k²) keys, by Lemma 2, and one broadcast. For each p ∈ L_X also compute A_X(p) = max_{v ∈ V(X)} d_G(v,p) in the same way.

Each step costs Õ(D²) rounds per depth, and there are O(log n) depths.

## 5. Eccentricities

For u, and each bag X on its chain, let E_X(u) be the maximum of:
- (a) d_G(u,p) for p ∈ L_X, known by the invariant;
- (b) A_X(u), if u ∈ L_X;
- (c) if X is no leaf and u is off P_X: for each face Φ′ and pattern on it, the value of Lemma 1 with the token's offset and pattern in the place of t_v. On the face of u itself the token must have another child than u. Otherwise it is the token of largest offset. The first term of Lemma 1 is known to u by the invariant, so no table on L_X × L_X is needed.

Let E(u) = max E_X(u) over the chain. All of this is local.

**Lemma 4.** E(u) is the eccentricity of u.

*Proof.* A token is attained by some v. For (c) Lemma 1 gives d_G(u,v), so E(u) is at most the eccentricity. Conversely let v be any vertex, and let X be the last bag on both chains. If u ∈ L_X, then (b) covers v. If v ∈ L_X, then (a). Otherwise both are off P_X, X is no leaf and both continue into different children. So the pair satisfies Lemma 1. The token for the pattern of v has at least the offset of v, and the value of Lemma 1 grows with the offset. If v is on the face of u, then v has another child than u, so one of the two stored offsets is admitted and it is at least the offset of v. ∎

The diameter and radius follow by one convergecast over T. This proves the theorem. ∎

Tokens can carry the identifier of a vertex that attains them, and so can A_X, so every vertex also learns a farthest vertex.

**Sum Corollary.** In Õ(D²) rounds every vertex u learns S(u) = Σ_v d_G(u,v). So the closeness of every vertex, a medoid and the Wiener index are computed in Õ(D²) rounds, deterministically. Importance if it survives: modest. To our knowledge there is no earlier CONGEST bound for these on planar networks.

For v ∈ V(X) off S_X let Y(v) be its unique child, by (H3). Each p ∈ L_X off S_X broadcasts Y(p) over T_X. Add to each non-leaf bag X, with one word per value since values are at most n(D + k):
- (A) For each face and pattern, the count and the sum of offsets of the vertices of X° off P_X, by a convergecast over T_X as in Step 5.
- (B) For each child Y, the same over the vertices of Y° off P_X, by a convergecast and a broadcast over T_Y. These are O(k²) keys per child, and children run in parallel by (H2).
- (C) For p ∈ S_X, the sum of d_G(v,p) over v ∈ X°. For p ∈ L_X off S_X, the sum over v ∈ X° off S_X, and the sum over v ∈ Y(p)° by a convergecast over T_{Y(p)}. Each result is returned to p by a broadcast.

Let S_X(u) be the sum of d_G(u,v) over the v for which X is the last bag on both chains. These sets of v partition V along the chain of u, so S(u) = Σ_X S_X(u). All of S_X(u) is known to u locally:
- If X is a leaf, then all v lie in X° ⊆ L_X, and the invariant gives the values.
- If u ∈ S_X, then v runs over X°, and S_X(u) is the first sum of (C).
- Otherwise v runs over S_X ∩ X° and over the vertices of X° off S_X in other children than Y(u). The first part is known by the invariant. If u ∈ L_X, the second part is the difference of the two sums of (C). If u is off P_X, take the vertices of L_X ∩ X° off S_X in other children by the invariant, and those off P_X by Lemma 1, which gives d_G(u,v) = off_v + M_u(Φ_v, π_v), where π_v(o′) is the value of t_v at o′ minus the offset of v, a prefix sum of the pattern, and

      M_u(Φ,π) = min { d_G(u, x(o′)) + π(o′) : o′ on Φ, x(o′) ∈ V(X) }.

  So the sum over those v is Σ_{(Φ,π)} (sum + count·M_u(Φ,π)) with the entries of (A), minus the same expression with the entries of (B) for Y(u). The subtraction is linear, so it does not matter that the formula need not give d_G(u,v) for v in the child of u. ∎

With integer vertex weights of O(log n) bits, the weighted sums follow in the same way; the simulator does not run this form.

## 6. Checks

Results are in `sim/diameter/REPORT.md`. `diam.py` builds real region bags and checks Lemmas 1, 2 and 3, the alternation, Fact 0 through the first-hit formula, the formula of Step 2, and finally E(u) against BFS for every vertex. Negative controls in `diam.py ctl`. `diam.py sum` checks S(u) from the tables of the Sum Corollary against BFS, with its own controls.

## 7. Not covered by the checks

- Rounds, messages and who knows what: no CONGEST simulation, in particular of Step 1, of the construction of bags, of the tables of the Sum Corollary and of lockstep scheduling. Word and round counts are by the proofs, and the simulator only counts tokens and dictionary entries.
- Word counts as D and n grow fit polylogarithmic factors, but these sizes cannot separate them from small powers.
- [1], [2], [4] and [5] at the source, and the proofs of Lemmas B1 and B5, except that the simulator exercises their statements on its instances.
- Sizes above about 500 vertices.

## 8. Open

- Õ(D) or a lower bound. Some faces have Ω(k²) patterns [4], so by counting patterns alone this token scheme cannot go below D² words in a bag; dominated tokens could still be dropped.
- Weighted graphs. Patterns are unbounded there.

## References

1. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019.
2. V. Fredslund-Hansen, S. Mozes, O. Weimann. A Tight Bound for Facial Distance Patterns in Planar Graphs. arXiv:2608.07187.
3. S. Senge. Exact shortest paths and flows on planar graphs. https://github.com/ssenge/ExactShortestPathsAndFlowsOnPlanarGraphs
4. S. Mozes, N. Wallheimer, O. Weimann. Improved Compression of the Okamura-Seymour Metric. ISAAC 2022.
5. C. Lenzen, D. Peleg. Efficient distributed source detection with limited bandwidth. PODC 2013.
6. V. Fredslund-Hansen, S. Mozes, C. Wulff-Nilsen. Truly subquadratic exact distance oracles with constant query time for planar graphs. ISAAC 2021.
