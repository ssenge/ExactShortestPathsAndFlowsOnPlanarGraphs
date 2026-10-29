# Lemma S: the recursion of Theorem D

*Status (2026-10-29).* New. The defect was found by the adversarial pass on Lemma R
(sim/thmD/attackR). Proof written here; no referee pass yet. Tests in sim/thmD (below).

Theorem D (NOTES.md §5) runs the recursion ShortestCycle of [18, Alg. 3] with exact trees. Its
proof said that the minimum over the computed P_t is the minimum cut. As written, the recursion
can miss it. This note gives an instance, a repair that costs two more SSSP calls per level, and
a proof that the repaired recursion finds the minimum cut. Lemma R and Lemma N
(GHAT_REPAIR.md) are not affected.

## The defect

After computing P_i in an annulus A with index range [j, k], the recursion drops every index t
with i1 < t < i2, where i1 and i2 are the least and greatest index of a copy of P on P_i
([18, Alg. 3, lines 15 to 19; Lemma 5.6]). The children get the ranges [j, i1] and [i2, k]. The
justification is [18, Claim 2.4]: P_{i1} or P_{i2} is no longer than P_t. But A can hold copies
of P outside [j, k], so i1 < j or i2 > k is possible (the driver counts this as i12_outside).
The witness P_{i1} or P_{i2} then lies outside the range of A, and may itself have been dropped
earlier. Two drops can rest on each other, and no computed path has the minimum length.

Smallest instance found (simple graph, n = 11, m = 22, s = 5, t = 3; data and trace in
sim/thmD/attackR/logs/trace_min_simple0.txt):

- ends (0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),
  (5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)
- capacities 1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2
- rotation [0,38,2,25], [1,34,30,6], [3,40,31,4,33], [7,41,39], [11,12,18], [13,28,20,27,23],
  [22,43], [24,8,16,5,35], [9,32,36,10,14,21], [15,19,42,26], [17,29,37] (dart 2e leaves the
  first end of edge e)

The minimum cut is 15 (edges 4, 8, 16; networkx, sim/thmD/fix/verify_min.py). With f = face 12,
g = face 1 and the corners of the trace, P has faces 12, 10, 9, 8, 5, 3, 0, 1. The minimum cycle
C* is the dual triangle (p_4, p_5, face 7). It uses the edge of P between p_4 and p_5, so it
serves as both P_4 and P_5.

1. Level 1, range [0, 7]: P_3 = p_3^0 f_7 p_5^1 p_4^1 p_3^1 (length 99), so i1 = 3, i2 = 5.
   Index 4 is dropped with P_5 as its witness. The children have ranges [0, 3] and [5, 7].
2. Level 2, range [5, 7]: this annulus also holds p_3^0 and p_4^0, and the distance between
   p_5^0 and p_5^1 in it is 15. P_6 = p_6^0 p_5^0 p_4^0 f_4 f_6 p_7^1 p_6^1 (length 37), so
   i1 = 4 < 5. Index 5 is dropped with P_4 as its witness, which level 1 already dropped.
3. The recursion reports 37, which is 2.47 times the minimum.

Every shortest path taken is unique, so no tie-break avoids this. Clamping i1 and i2 to [j, k]
does not help either: the two copies of p_5 end up in different children. The repository driver
(sim/thmD/thmD.py) reports 37 on 2 of 80 runs of this instance (the runs differ in f, g and the
corners), and wrong values on all 25 instances of the adversarial search (161 of 300 runs). The
search found 5 such instances in 1.5 million simple graphs with generic capacities and 40 in
1 million multigraphs with n ≤ 12.

As we read [18], its own recursion is the same, and exact trees are a special case of its
approximate ones, so [18, Thm 1.1] would inherit the defect. We have not checked whether
another reading of [18, Lemma 5.6] avoids it.

## The repair

In every annulus A that is not a leaf, after P_i, i1 and i2 are known, also compute P_a and P_b
in A for

  a = max(i1, j),  b = min(i2, k)

(skip one that equals i). Nothing else changes: the same indices are dropped, the children,
the incisions and Ĝ_ℓ are the same. P_a and P_b are computed like P_i: one SSSP call with one
source per annulus, all annuli of a level at once, so two more calls per level and the same
Õ(D) bound. The indices a and b are known to all nodes of A after the aggregation of
[18, Lemma 5.6].

## Setting

- All lengths are w = K·c + 1 on dual edges (NOTES §5, weights). They are positive, and every
  tree path of Theorem D is w-shortest. Since K exceeds the hop length of every simple path,
  ⌊Λ / K⌋ is the minimum cut λ, where Λ = min_t λ_t below (the Reif reduction of
  GHAT_REPAIR.md for lengths c, plus the hop count below K).
- P = p_0 … p_m is a w-shortest f-to-g path in G* ([18, Alg. 3, line 2], computed exactly).
  d(u, v) denotes the w-length of P[u..v]. Positions along P strictly increase with the index.
- A_1 is the level-1 annulus (the cut along γ, Lemma N). It has one piece p_t^0 and one piece
  p_t^1 for each t, and B^σ[u→v] denotes the σ-copy of P[u..v] in A_1, a path of length d(u, v).
  λ_t is the distance in A_1 from p_t^0 to p_t^1, and Λ = min_t λ_t.
- A level-ℓ annulus A has a range [j_A, k_A] of indices t for which it computes P_t
  ([18, Sec. 5.1]). By Lemma N each piece of A refines one piece of A_1 and each edge of A is a
  pair of the same weight, so every walk in A maps to a walk in A_1 of the same length, and a
  piece of p_t^σ maps to p_t^σ. We use this map without naming it.

## Facts

- **(P)** A walk in A_1 from a copy of p_u to a copy of p_v has length at least d(u, v). Its
  image in G* is a walk from p_u to p_v, and P is shortest.
- **(B)** If Z is a walk in A_1 from p_u^0 to p_v^1, then λ_q ≤ d(q, u) + w(Z) + d(v, q) for
  every q: take B^0[q→u], then Z, then B^1[v→q].
- **(W)** Let W be a walk in A_1 from p_t^0 to p_t^1 that visits p_u^0 and p_v^1, in either
  order. Then λ_q ≤ w(W) for every q between min(t, u, v) and max(t, u, v).
  *Proof.* Let Z be the part of W between the two visits, read from p_u^0 to p_v^1. By (P) on
  the two other parts, w(W) ≥ d(t, u) + w(Z) + d(v, t). By (B), λ_q ≤ d(q, u) + w(Z) + d(v, q).
  The function g(q) = d(q, u) + d(q, v) is constant between u and v and grows away from them,
  so g(q) ≤ g(t) for every q in the stated range. ∎
- **(O)** ([18, Remark 2.5, Fig. 11]; side order.) Let Q = P_i′ run from a piece of p_x^0 to a
  piece of p_y^1. Incising Q splits A into subgraphs, each on one side of Q. On one side lie
  the pieces of p_t^0 for t < x and of p_t^1 for t < y; on the other those of p_t^0 for t > x
  and of p_t^1 for t > y. The two ends of Q split, one piece on each side. Nodes and edges off
  Q do not change (F2). Hence, for t strictly between x and y with both pieces in A, every
  path in A from p_t^0 to p_t^1 meets a node of Q. We call this (S).
- **(INV)** For a level-ℓ annulus A and t ∈ [j_A, k_A], A contains a piece of p_t^0 and a
  piece of p_t^1, and their distance in A is λ_t.
  *Proof.* At level 1 by definition. Let A be a parent with (INV), Q its incised part with ends
  at x and y, and A′ the child with range [i2, k_A] (the other child is symmetric). By the
  lemma below, i2 = max(i, x, y), so every t in [i2, k_A] has both pieces on the side of A′
  by (O) (a junction piece goes to A′ as its own piece). Let W be a shortest path in A from
  p_t^0 to p_t^1. If W meets Q, let z_1 and z_2 be its first and last nodes on Q and replace
  W[z_1..z_2] by Q[z_1..z_2], a subpath of the shortest path P_i. The length does not grow, the
  new path meets Q only along Q[z_1..z_2], and its two ends lie on the side of A′. So it lies
  in A′, using the pieces of Q on that side. Hence the distance in A′ is λ_t. This is the exact
  exchange of NOTES §5, used for [18, Lemma 2.7]. ∎

## Lemma S1 (interval form of [18, Claim 2.4])

Let A satisfy (INV), i ∈ [j_A, k_A], P_i a shortest path in A from p_i^0 to p_i^1, Q = P_i′ with
ends at x and y as in (O), and i1, i2 the least and greatest index of a copy of P on P_i. Then
i1 = min(i, x, y) and i2 = max(i, x, y), and for every t ∈ [j_A, k_A] with i1 < t < i2,

  λ_q ≤ λ_t for all q ∈ [i1, t],  or  λ_q ≤ λ_t for all q ∈ [t, i2].

*Proof.* Write P_i = U·Q·V, with U from p_i^0 to p_x^0 and V from p_y^1 to p_i^1. By (INV),
w(P_i) = λ_i, so P_i is no longer than any walk in A_1 from p_i^0 to p_i^1.

(a) w(U) = d(i, x) and w(V) = d(y, i). Indeed ≥ holds by (P), and ≤ holds because
B^0[i→x]·Q·V and U·Q·B^1[y→i] are walks from p_i^0 to p_i^1. So
w(P_i) = w(Q) + d(i, x) + d(i, y).

(b) A copy of p_r on U gives d(i, r) + d(r, x) ≤ w(U) = d(i, x) by (P), so r lies between i and
x, since edges of P have positive length. Likewise a copy on V lies between y and i, and Q has
no copy of P inside. Hence i1 = min(i, x, y) and i2 = max(i, x, y).

Let J be the interval between m1 = min(x, y) and m2 = max(x, y), and f(q) = d(q, x) + d(q, y).
Then f is constant on J and f(q) = f(m1) + 2·(distance along P from q to J) off J.

(c) Two bounds. By (B) with Z = Q, λ_q ≤ w(Q) + f(q) for every q. And B^0[i→t]·W_t·B^1[t→i],
with W_t a shortest path from p_t^0 to p_t^1, is a walk from p_i^0 to p_i^1, so
λ_i ≤ λ_t + 2 d(i, t), that is, λ_t ≥ w(Q) + f(i) − 2 d(i, t).

*Case 1: t is not strictly inside J.* Since i1 < t < i2, i lies outside the interior of J and t
lies between i and J, possibly at its near end. Then f(t) = f(i) − 2 d(i, t), so by (c)
λ_t ≥ w(Q) + f(t) ≥ w(Q) + f(q) ≥ λ_q for every q with f(q) ≤ f(t). These are all q between t
and the far end of J. If i < t this is [t, m2] = [t, i2]; if i > t it is [m1, t] = [i1, t].

*Case 2: m1 < t < m2.* By (S), W_t meets Q at a node z. Split W_t = X·Y and Q = Q1·Q2 at z, with
Q1 from p_x^0 to z. The walks B^0[i→t]·X·Q2·V and U·Q1·Y·B^1[t→i] run from p_i^0 to p_i^1, so
by (a)

  w(X) ≥ w(Q1) + d(i, x) − d(i, t),   w(Y) ≥ w(Q2) + d(i, y) − d(i, t).

Let i ≤ t. Then i2 = m2, and t lies between i and m2.
- If m2 = y, let W′ = X·Q2·B^1[y→t]. Then
  w(W′) = w(X) + w(Q2) + d(y, t) ≤ w(X) + w(Y) − d(i, y) + d(i, t) + d(t, y) = λ_t.
  W′ visits p_t^0 and p_y^1, so by (W), λ_q ≤ λ_t for q ∈ [t, y] = [t, i2].
- If m2 = x, let W″ = B^0[t→x]·Q1·Y. In the same way w(W″) ≤ λ_t, and W″ visits p_x^0 and
  p_t^1, so λ_q ≤ λ_t for q ∈ [t, x] = [t, i2].

If i ≥ t, the same argument with m1 = i1 gives λ_q ≤ λ_t for q ∈ [i1, t]. ∎

Note that the witness interval reaches i1 or i2 itself, not only a point inside A. This is what
the recursion of [18] misses: the end it needs can lie outside [j_A, k_A].

## Lemma S2 (the repaired recursion is exact)

With the repair, the least computed length is Λ, so ⌊·/K⌋ of it is the minimum cut.

*Proof.* Every computed length is the length of a path in an annulus between pieces of p_t^0 and
p_t^1, or of the walk through a node of the overlap rule ([18, Alg. 3, lines 9 to 14]). It maps
to a walk in A_1 from p_t^0 to p_t^1, so it is at least λ_t ≥ Λ.

Call an annulus A good if λ_t = Λ for some t ∈ [j_A, k_A]. A_1 is good, with range [0, m]. We
show: if A is good, then Λ is computed in A or a child of A is good. The recursion is finite,
so Λ is computed somewhere. Fix t ∈ [j_A, k_A] with λ_t = Λ.

- *A is a leaf.* It computes P_{j_A} and P_{k_A}, of lengths λ_{j_A} and λ_{k_A} by (INV), and
  t is one of them.
- *i1 < t < i2.* By Lemma S1, Λ = λ_q for all q ∈ [i1, t] or for all q ∈ [t, i2]. Since
  j_A ≤ t ≤ k_A, a = max(i1, j_A) lies in [i1, t] and b = min(i2, k_A) in [t, i2]. Both lie in
  [j_A, k_A], so the repair computes λ_a and λ_b by (INV), and one of them is Λ.
- *t ≤ i1.* If the side of [j_A, i] has an overlap, lines 9 to 14 compute P_m for all
  m ∈ [j_A, i] through a common node, and their lengths are λ_m by (INV) and [18, Claim 2.3]
  (exact form, NOTES §5). Otherwise that side is the child with range [j_A, i1] (a side is
  discarded only when P_i meets the bounding path on that side, F3), and it is good by (INV).
- *t ≥ i2.* Symmetric. ∎

## Tests (sim/thmD)

- fix/: verify_min.py checks the instance above (minimum cut 15, planar rotation).
  confirm_ends.py runs the driver on the 25 instances of the adversarial search, 12 runs each:
  161 of 300 runs give a wrong value without the repair (logs/ends0.jsonl), 0 of 300 with it
  (logs/ends1.jsonl, logs/ends1b.jsonl with the check of Lemma S1).
- thmD.py --ends 1 adds the repair and three checks: c24_interval (the conclusion of Lemma S1,
  with λ from A_1), hull_i12 (part (b)) and sep_fail (fact (S) after the incision).
  lane_ends.sh runs the driver's families with and without the repair on the same seeds;
  lane_c24.sh and lane_sep.sh run the checks.
- Without the repair the driver's own families hit the defect too: 6 wrong values in
  1,200,000 instances (1 in 300,000 small, 1 in 300,000 tiny, 2 in 300,000 with up to 70
  vertices under each tie-break; logs/ends0_*.json).
- With the repair, no check failed in 1,740,000 instances on the same seeds and more: 300,000
  small, 300,000 tiny, 600,000 with up to 70 vertices under two tie-breaks, 40,000 with up to
  160 vertices and 200,000 with many equal capacities (logs/ends1_*.json). The computed
  lengths at a and b always equal λ_a and λ_b, as (INV) says.
- The conclusion of Lemma S1 held in 460,000 further instances, 89,951 of them with a dropped
  index in range (logs/c24_*.json, logs/sep_*.json). Fact (S) and part (b) held in the 210,000
  of logs/sep_*.json, 23,910 of them with an index strictly between x and y in range.

## Points of doubt

- (O) is taken from [18, Remark 2.5] and the planar picture, not proved from tokens here. Lemma
  N proves how pieces split, but not which side of Q each copy of P ends on. The driver checks
  (S) directly.
- The overlap rule ([18, Claim 2.3]) is used as in NOTES §5, in its exact form.
