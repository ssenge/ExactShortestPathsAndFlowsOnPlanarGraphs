# Lemma S: the recursion of Theorem D

*Status (2026-10-29).* The defect was found by the adversarial pass on Lemma R
(sim/thmD/attackR). Referee pass on the first version (2026-10-29): correct with gaps, nothing
fatal. The referee checked the algebra of Lemma S1 and the logic of Lemma S2 in full. Its two
serious points are older gaps of Theorem D, not new ones. One is the side fact (O): which side
of an incision each copy of P lands on. The other is the exact form of [18, Claim 2.3]. This
revision changes four things:
- Lemma S1 now runs in A_1 and needs neither of the two gaps. Its separation step (S_1) is
  proved here by a parity argument.
- The level-ℓ facts are collected as Lemma O. Its proof is now written (LEMMA_O.md), with
  five changes to the statement; it has had no referee pass yet.
- The minor points are fixed.
- The test counts are corrected.

Theorem D (NOTES.md §5) runs the recursion ShortestCycle of [18, Alg. 3] with exact trees. Its
proof said that the minimum over the computed P_t is the minimum cut. As written, the recursion
can miss it. This note gives:
- an instance;
- a repair that costs two more SSSP calls per level;
- a proof that the repaired recursion finds the minimum cut, given Lemma O (LEMMA_O.md).

Lemma R and Lemma N (GHAT_REPAIR.md) are not affected.

## The defect

After computing P_i in an annulus A with index range [j, k], the recursion drops every index t
with i1 < t < i2. Here i1 and i2 are the least and greatest index of a copy of P on P_i
([18, Alg. 3, lines 15 to 19; Lemma 5.6]). The children get the ranges [j, i1] and [i2, k]. The
reason given is [18, Claim 2.4]: P_{i1} or P_{i2} is no longer than P_t. Reif's own recursion
([18, Alg. 1]) drops nothing; the drop is new in [18].

The proof of [18, Lemma 5.6] assumes that "the p_j-to-p_k subpath P′ of P has two copies in A".
Under that assumption i1 and i2 lie in [j, k], every range end is computed, and the recursion
would be correct. But A can hold copies of P outside [j, k]: the driver counts i1 < j or i2 > k
as i12_outside. The witness P_{i1} or P_{i2} then lies outside the range of A, and another
annulus may have dropped it already. Two drops can rest on each other, and then no computed
path has the minimum length.

Smallest instance found (simple graph, n = 11, m = 22, s = 5, t = 3). Data and trace are in
sim/thmD/attackR/logs/trace_min_simple0.txt; the lengths below are capacities c.

- ends (0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),
  (5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)
- capacities 1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2
- rotation [0,38,2,25], [1,34,30,6], [3,40,31,4,33], [7,41,39], [11,12,18], [13,28,20,27,23],
  [22,43], [24,8,16,5,35], [9,32,36,10,14,21], [15,19,42,26], [17,29,37] (dart 2e leaves the
  first end of edge e)

The minimum cut is 15: edges 4, 8 and 16, by networkx in sim/thmD/fix/verify_min.py. Take
f = face 12, g = face 1 and the corners of the trace. Then P has faces 12, 10, 9, 8, 5, 3, 0, 1.
The minimum cycle C* is the dual triangle (p_4, p_5, face 7). It uses the edge of P between p_4
and p_5, so it serves as both P_4 and P_5.

1. Level 1, range [0, 7]: P_3 = p_3^0 f_7 p_5^1 p_4^1 p_3^1 (length 99), so i1 = 3 and i2 = 5.
   Index 4 is dropped with P_5 as its witness. The children have ranges [0, 3] and [5, 7].
2. Level 2, range [5, 7]: this annulus also holds p_3^0 and p_4^0, and the distance between
   p_5^0 and p_5^1 in it is 15. P_6 = p_6^0 p_5^0 p_4^0 f_4 f_6 p_7^1 p_6^1 (length 37), so
   i1 = 4 < 5. Index 5 is dropped with P_4 as its witness, which level 1 already dropped.
3. The recursion reports 37, which is 2.47 times the minimum.

**No reading we tried avoids it.**
- Every shortest path taken is unique, so no tie-break helps.
- Clamping i1 and i2 to [j, k] does not help either: the two copies of p_5 end up in different
  children. The same holds if one aggregates only over the copies of P[j..k].
- The sub-range j ≤ j′ ≤ k′ ≤ k of [18, Sec. 5.1] changes only the overlap rule, and the
  instance has no overlap.

**How often it happens.**
- The repository driver (sim/thmD/thmD.py) reports 37 on 2 of 80 runs of this instance; the
  runs differ in f, g and the corners.
- The adversarial runs met the defect 54 times, counting runs. Its two searches found 45
  instances: 40 in 1 million multigraphs with n ≤ 12, and 5 in 1.5 million simple graphs with
  generic capacities.
- The 25 instances it saved (20 + 5) give wrong values on the driver too, in 161 of 300 runs.

As we read [18], its own recursion is the same, and exact trees are a special case of its
approximate ones, so [18, Thm 1.1] would inherit the defect. The step of [18, Sec. 5.2] that
says the leaf annuli cover all of P is where the defect bites.

## The repair

In every annulus A that is not a leaf, once P_i, i1 and i2 are known, also compute P_{i⁻} and
P_{i⁺} in A for

  i⁻ = max(i1, j_A),  i⁺ = min(i2, k_A)

(skip one that equals i). Nothing else changes: the same indices are dropped, and the
children, the incisions and Ĝ_ℓ stay the same.
- **Cost.** The two paths are computed like P_i: one SSSP call with one source per annulus,
  all annuli of a level at once. That is two more calls per level and the same Õ(D) bound.
- **Local knowledge.** Every node of A knows i1 and i2 after [18, Lemma 5.6], and j_A and k_A
  by [18, Sec. 5.1], so it computes i⁻ and i⁺ locally. The source is elected as for P_i.
- **Use of the results.** The two paths are marked as tree paths (Lemma 5.2 of [18]) and enter
  the final minimum and the cut extraction of [18, Sec. 5.2]. That extraction gives a cut of
  weight equal to the path length for them too.
- **Ties.** Among the computed paths of least length, take the one with the least index t; at
  equal t, take the first computed.

Computing P_{j_A} and P_{k_A} in every annulus instead would also work, at the same cost.
Lemma S1 below proves that too.

## Setting

- **Lengths.** All lengths are w = K·c + 1 on dual edges (NOTES §5, weights). They are
  positive, and every tree path of Theorem D is w-shortest. K exceeds the hop length of every
  simple path, so w-shortest means shortest for c, with fewer hops breaking ties. The driver
  takes K per level, which is the same.
- **The path P.** P = p_0 … p_m is a w-shortest f-to-g path in G* ([18, Alg. 3, line 2],
  computed exactly), hence also c-shortest. d(u, v) denotes the w-length of P[u..v]. Positions
  along P strictly increase with the index.
- **The level-1 annulus.** A_1 is the cut along γ (Lemma N). It has one piece p_t^0 and one
  piece p_t^1 for each t. B^σ[u→v] denotes the σ-copy of P[u..v] in A_1, a path of length
  d(u, v). λ_t is the w-distance in A_1 from p_t^0 to p_t^1, and Λ = min_t λ_t.
- **⌊Λ / K⌋ = λ, the minimum cut.** By the Reif reduction (GHAT_REPAIR.md), every walk in A_1
  from p_t^0 to p_t^1 has c-length at least λ, so its w-length is at least Kλ + 1. The
  reduction also gives a simple path of c-length λ, with fewer than K hops, so Λ < K(λ + 1).
- **Annuli.** A level-ℓ annulus A has a range [j_A, k_A] of indices t for which it computes
  P_t ([18, Sec. 5.1]). By Lemma N each piece of A refines one piece of A_1, and each edge of A
  is a pair of the same weight. So every walk in A maps to a walk in A_1 of the same length,
  and a piece of p_t^σ maps to p_t^σ. We use this map without naming it.
- **Orientation.** For a walk P̄ from p_i^0 to p_i^1, x is the index of the last 0-copy on P̄
  and y that of the first 1-copy after it. The part Q̄ of P̄ between them has no copy of P
  inside. For P_i this Q̄ is the incised part P_i′ ([18, Lemma 5.7]). P_i is read from p_i^0;
  if the tree was rooted at p_i^1, reverse the path first.

## Facts in A_1

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
- **(S_1)** Let Q̄ be a walk in A_1 from p_x^0 to p_y^1 with no copy of P inside, and let t lie
  strictly between x and y. Then every walk W in A_1 from p_t^0 to p_t^1 meets a node of Q̄.
  *Proof.* Suppose W meets no node of Q̄.
  - Draw both walks as in the (≥) half of the Reif reduction. Each pair becomes a short curve
    across its edge, and each visit to a piece becomes a curve inside that piece's side of γ.
    Since W and Q̄ share no node, the two curves are disjoint.
  - Keep W's curve out of a thin neighbourhood N of γ. Its crossings of P's edges can sit
    near the ends of those edges, away from γ.
  - Close W inside the face p_t by an arc from the side-0 part to the side-1 part. This arc
    crosses γ once.
  - Close Q̄ by a run inside N on the 1-side of γ, from the face p_y back to p_x, and then
    across γ inside p_x into the side-0 part.
  - The run passes through the side-1 part of p_t, because t lies between x and y. W's closing
    arc crosses it there exactly once. No other pair of parts meets: W's curve avoids N, Q̄'s
    curve avoids the pieces of W, and the closing parts meet only inside p_t.
  - So the two closed curves cross exactly once. Two closed curves on the sphere in general
    position cross an even number of times, a contradiction. ∎

## Lemma O (sides of one incision)

The level-ℓ facts below are what the recursion needs beyond A_1. The exact exchange of
NOTES §5 already used them for [18, Lemma 2.7]. In the first version they were taken from
[18, Remark 2.5] and the planar picture; the referee found them true in substance, but not
proved from Lemma N and F1 to F5, which are local. LEMMA_O.md proves them by an induction over
the levels, in a curve model: each incision is drawn as an arc C_Q, closed by a part of γ into a
simple closed curve J_Q, and "side" means a side of J_Q. Four standard facts of plane topology
are used (Jordan, θ-curve, parity of crossings, one transversal crossing switches sides).

Along with Lemma O the induction proves an invariant (I) of every live annulus (LEMMA_O.md §3):
it is a component of G*_ℓ (I0); the slots of its pieces and the curves of its bounding paths
have a fixed shape (I1); its bounding paths P_a and P_b run from a piece of p^0 to a piece of
p^1 at the low or high ends (I2); it has at most one piece of each face, and pieces of p_t^0
and p_t^1 exactly on two index intervals that contain its range (I3); its old pairs are copies
of P or lie on P_a or P_b (I4); and (I5) below. A_1 satisfies (I), and so does every called
child.

Let A be a live annulus of level ℓ that is not a leaf and satisfies (I). Let P_i be its path,
and Q = P_i′ its incised part from a piece g_x of p_x^0 to a piece g_y of p_y^1.
- **(O1)** Every subgraph obtained by incising Q lies on one side of J_Q. A's pieces of p_t^0
  for t < x and of p_t^1 for t < y lie on the low side; those with t > x and t > y on the high
  side. If Q's edge at g_x is new, g_x splits into its part below the cut, on the low side, and
  its part above it, on the high side. If that edge is old, it is the first edge of P_a or of
  P_b; g_x does not split, and it lies on the high side if the edge is on P_a and on the low
  side if it is on P_b. Then P_i meets that path at g_x, so its side gets no call, and the
  called side, if any, holds all of g_x. The same holds at g_y with the last edge. For t
  strictly between x and y, every walk in A from A's piece of p_t^0 to its piece of p_t^1
  meets a node of Q. (The first version said that both ends always split, which is false for
  old end edges.)
- **(O2)** A side on which P_i does not meet the bounding path is one subgraph. It has no bad
  edge, and it holds exactly one copy of each edge of Q. A bad edge in a subgraph of the j-side
  is an edge of P_a; on the k-side, of P_b.
- **(O3)** Every live annulus has at most one piece of each p_t^σ and of each face off P.
- **(INV)** For every live annulus A and every t such that A has pieces of p_t^0 and p_t^1, in
  particular every t ∈ [j_A, k_A], their distance in A is λ_t. The proof for a called child
  replaces the part of a shortest walk between its first and last node on Q by the part of Q in
  between, lifted to the called side; this works because that side holds exactly one part of
  each node of Q. It covers t = i2 at a junction and walks that touch Q in one node.
- **(C23)** If P_i meets P_a in a node z, then d_A(g_m^0, z) + d_A(z, g_m^1) = λ_m for every
  m ∈ [max(x_a, y_a), i], where x_a and y_a are the indices of the ends of P_a. By (I3) this
  interval contains [j_A, i]. So any common node serves as the source of the overlap rule, which
  then computes λ_m exactly for every m ∈ [j_A, i]. The k-side is symmetric. Beyond i the
  equality fails in general (1,669 of 12,044 test checks on (i, i2]). This replaces
  [18, Claim 2.3], which is stated for annuli that hold exactly the copies of their range and are
  bounded by full paths P_k. The proof is a parity argument in the style of (S_1).

What is taken from [18]: the structure of the recursion [18, Alg. 3] (which path, the overlap
rule, which sides get a call with which range), and incision as a split of nodes
[18, Def. 2.2, Remark 2.5] in the token form of Lemma N. Matching [18]'s two sides to the low and
high sides is a reading, the same one Lemma N and the driver make. [18, Claim 2.3] is not used,
nor F2, F4 or F5 of GHAT_REPAIR.md, nor the converse of [18, Claim 5.8].

## Lemma S1 (interval form of [18, Claim 2.4])

Let P̄ be a walk in A_1 from p_i^0 to p_i^1 of length λ_i. Let x, y and Q̄ be as under
Orientation, and let i1 and i2 be the least and greatest index of a copy of P on P̄. Then
i1 = min(i, x, y) and i2 = max(i, x, y), and for every t with i1 < t < i2,

  λ_q ≤ λ_t for all q ∈ [i1, t],  or  λ_q ≤ λ_t for all q ∈ [t, i2].

By (INV), the image of P_i is such a walk. No other level-ℓ fact is used.

*Proof.* Write P̄ = U·Q̄·V, with U from p_i^0 to p_x^0 and V from p_y^1 to p_i^1. P̄ has length
λ_i, so it is no longer than any walk in A_1 from p_i^0 to p_i^1.

(a) w(U) = d(i, x) and w(V) = d(y, i). The bound ≥ holds by (P). The bound ≤ holds because
B^0[i→x]·Q̄·V and U·Q̄·B^1[y→i] are walks from p_i^0 to p_i^1. So
w(P̄) = w(Q̄) + d(i, x) + d(i, y).

(b) A copy of p_r on U gives d(i, r) + d(r, x) ≤ w(U) = d(i, x) by (P). So r lies between i and
x, since edges of P have positive length. U may hold 1-copies; they obey the same bound. V holds
no 0-copy, by the choice of x, and its copies lie between y and i. Q̄ has no copy inside. Hence
i1 = min(i, x, y) and i2 = max(i, x, y).

Let J be the interval between m1 = min(x, y) and m2 = max(x, y), and let
f(q) = d(q, x) + d(q, y). Then f is constant on J, and off J,
f(q) = f(m1) + 2·(distance along P from q to J).

(c) Two bounds. By (B) with Z = Q̄, λ_q ≤ w(Q̄) + f(q) for every q. Let W_t be a shortest walk
in A_1 from p_t^0 to p_t^1. Then B^0[i→t]·W_t·B^1[t→i] is a walk from p_i^0 to p_i^1, so
λ_i ≤ λ_t + 2 d(i, t), that is, λ_t ≥ w(Q̄) + f(i) − 2 d(i, t).

*Case 1: t is not strictly inside J.* Since i1 < t < i2, i lies outside the interior of J, and
t lies between i and J, possibly at its near end. Then f(t) = f(i) − 2 d(i, t). So by (c),
λ_t ≥ w(Q̄) + f(t) ≥ w(Q̄) + f(q) ≥ λ_q for every q with f(q) ≤ f(t). These are all q between t
and the far end of J. If i < t this is [t, m2] = [t, i2]; if i > t it is [m1, t] = [i1, t].

*Case 2: m1 < t < m2.* By (S_1), W_t meets Q̄ at a node z. Split W_t = X·Y and Q̄ = Q1·Q2 at z,
with Q1 from p_x^0 to z. The walks B^0[i→t]·X·Q2·V and U·Q1·Y·B^1[t→i] run from p_i^0 to
p_i^1, so by (a)

  w(X) ≥ w(Q1) + d(i, x) − d(i, t),   w(Y) ≥ w(Q2) + d(i, y) − d(i, t).

Let i ≤ t. Then i2 = m2, and t lies between i and m2.
- If m2 = y, let W′ = X·Q2·B^1[y→t]. Then
  w(W′) = w(X) + w(Q2) + d(y, t) ≤ w(X) + w(Y) − d(i, y) + d(i, t) + d(t, y) = λ_t.
  W′ visits p_t^0 and p_y^1, so by (W), λ_q ≤ λ_t for q ∈ [t, y] = [t, i2].
- If m2 = x, let W″ = B^0[t→x]·Q1·Y. In the same way w(W″) ≤ λ_t, and W″ visits p_x^0 and
  p_t^1, so λ_q ≤ λ_t for q ∈ [t, x] = [t, i2].

If i ≥ t, the same argument with m1 = i1 gives λ_q ≤ λ_t for q ∈ [i1, t]. ∎

The witness interval reaches i1 or i2 itself, not just a point inside the range of A. The
recursion of [18] misses exactly this: the end it needs can lie outside [j_A, k_A].

## Lemma S2 (the repaired recursion is exact)

By Lemma O, the least computed length is Λ, so its ⌊·/K⌋ is the minimum cut.

*Proof.* Soundness first. Every computed length is the length of one of two things:
- a path in an annulus between its pieces of p_t^0 and p_t^1, which are unique by (O3); or
- a walk through a node of the overlap rule ([18, Alg. 3, lines 9 to 14]).

Either maps to a walk in A_1 from p_t^0 to p_t^1, so its length is at least λ_t ≥ Λ.

Call an annulus A good if λ_t = Λ for some t ∈ [j_A, k_A]. A_1 is good, with range [0, m]. We
show: if A is good, then Λ is computed in A, or a called child of A is good. The recursion is
finite, so Λ is computed somewhere. Fix t ∈ [j_A, k_A] with λ_t = Λ.

- *A is a leaf.* It computes P_{j_A} and P_{k_A}, of lengths λ_{j_A} and λ_{k_A} by (INV),
  and t is one of these two indices.
- *i1 < t < i2.* By Lemma S1, Λ = λ_q for all q ∈ [i1, t] or for all q ∈ [t, i2]. Since
  j_A ≤ t ≤ k_A, i⁻ lies in [i1, t] and i⁺ in [t, i2]. Both lie in [j_A, k_A], so the repair
  computes λ_{i⁻} and λ_{i⁺} by (INV), and one of them is Λ.
- *t ≤ i1.* Suppose the j-side has an overlap. Then lines 9 to 14 compute a length for every
  m ∈ [j_A, i] through a common node, and it is λ_m for m ∈ [j_A, i1] by (C23). Otherwise the
  j-side is the called child with range [j_A, i1], by (O2), and it is good by (INV).
- *t ≥ i2.* Symmetric. ∎

## Tests (sim/thmD)

- **fix/.** verify_min.py checks the instance above: minimum cut 15 and a planar rotation.
  confirm_ends.py runs the driver on the 25 saved instances of the adversarial search, 12 runs
  each. Without the repair 161 of 300 runs give a wrong value (logs/ends0.jsonl); with it, 0 of
  300 (logs/ends1.jsonl, and logs/ends1b.jsonl with the check of Lemma S1).
- **thmD.py --ends 1.** It adds the repair and three checks:
  - c24_interval: the conclusion of Lemma S1, with λ from A_1 in lengths c. This is the floor
    of the w-statement, so a weaker check.
  - hull_i12: part (b).
  - sep_fail: (S) at level ℓ, for t in range, after the incision.

  lane_ends.sh runs the driver's families with and without the repair on the same seeds;
  lane_c24.sh and lane_sep.sh run the checks. The ends1_* logs predate the three checks; they
  test the final value and every earlier check.
- **Without the repair.** The driver's own families hit the defect: 6 wrong values in
  1,200,000 instances. That is 1 in 300,000 small instances, 1 in 300,000 tiny ones, and 2 in
  300,000 with up to 70 vertices under each of two tie-breaks (logs/ends0_*.json).
- **With the repair.** No check failed in 1,440,000 instances (logs/ends1_*.json): the same
  1,200,000 seeds, 40,000 instances with up to 160 vertices, and 200,000 with many equal
  capacities. The computed lengths at i⁻ and i⁺ always equal λ, as (INV) says.
- **The checks.** c24_interval held in 460,000 further instances, 89,951 of them with a
  dropped index in range (logs/c24_*.json, logs/sep_*.json). hull_i12 and sep_fail held in
  the 210,000 instances of logs/sep_*.json, 23,910 of them with an index strictly between x
  and y in range.
- **lemmaO/.** patchO.py adds checks of every part of (I) and of Lemma O at every incision and
  every child to a copy of the driver. 342,000 instances with 232,868 incisions, no failed check
  (lane?.json). Among them: 72,697 incisions with x = y; 14,230 linear internal nodes of Q that
  split; 72,194 end pieces with an old end token, each on the predicted side; 417,577 sides
  without overlap, each one subgraph; 818,830 checks of (INV) at children; (I5) in the strong
  form for 205,947 indices, 10,829 outside the range; (C23) on [j_A, i] in 320,774 checks.
- **refereeS/.** This is the referee's instrumented copy of the driver, thmD_refS.py. It ran
  162,000 instances with no failure (r_*.txt). It checked:
  - Lemma S1 with w-lengths for every t in (i1, i2): 51,401 checks, 11,101 of them outside the
    range;
  - (S) in A for every t between x and y: 20,396 checks;
  - (S_1) in A_1: 24,687 checks;
  - (O1): no subgraph mixed the two sides, in 91,651 incisions;
  - the containment and distance parts of (INV) for every index of every called child: 316,328
    checks;
  - copies of P in each annulus form intervals;
  - an end of Q that did not split always came with an overlap.

## Points of doubt

- Lemma O (LEMMA_O.md) has had no referee pass yet. Its own points of doubt are in its §11:
  the four topology facts are used without proof; matching [18]'s sides to the low and high
  sides is a reading; the invariant (I) has many parts; an end piece of one token with an old end
  token never occurred in the tests.
- (S_1) is proved with the curve drawing of the Reif reduction, in words, as there.
