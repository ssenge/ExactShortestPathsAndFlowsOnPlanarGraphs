# Lemma O: the sides of one incision

*Status (2026-10-29).* Referee pass (2026-10-29): correct with minor gaps, no fatal or serious
error; Lemma O supplies what Lemma S2 uses, in the form S2 uses it. The thirteen minor points are
fixed in this version (§12). This note proves the level-ℓ facts
that Lemma S2 (RECURSION.md) takes from Lemma O. The proof is an induction over the levels. Together with Lemma O it proves an
invariant (I) of the live annuli (§3), and Lemma O is stated for annuli that satisfy (I). The
model is a drawing of the token graph on the sphere, in which every incision is a curve and
every side is a side of a simple closed curve. §0 lists what is proved and what changed;
§10 lists the tests; §11 lists the points of doubt.

## 0. Results and changes

**Proved here**, with the four standard facts T1 to T4 of §2.1 taken as known:
- (O1), with "side" meaning a side of a simple closed curve J_Q (Claim 3), including the rule
  for the ends of Q (Claim 6) and the separation (S) at level ℓ (Claim 10);
- (O2) (Claim 11), (O3) (Claim 12), and (INV) for every called child (Claim 13);
- (C23), in a stronger form (Claim 15);
- that every called child satisfies (I) again (Claim 14), and that A_1 satisfies it (Claim 2).

**Changes to the statement of RECURSION.md.**
1. *Ends of Q.* The rule is stated by positions on the arc of the end piece. Let ε_0 be the
   token of Q's first edge at the end piece g_x. The parts of g_x below the cut point of ε_0
   lie on the low side and the parts above it on the high side. If ε_0 is new, g_x splits
   into one part on each side. If ε_0 is old, it lies on P_a or on P_b. On P_a it is the first
   token of P_a, its cut point is the low end of g_x, and all of g_x lies on the high side.
   On P_b all of g_x lies on the low side. The same holds at g_y. So an unsplit end goes to
   the side away from the bounding path that carries its edge, and that path's side overlaps.
2. *Hypothesis.* "A satisfies (INV)" is replaced by "A satisfies (I)". (I) contains (INV)
   and holds for A_1 and for every called child, so nothing is lost.
3. *(INV)* is proved in a strong form: in every live annulus, for every t such that the
   annulus has a piece of p_t^0 and a piece of p_t^1, their distance is λ_t, also for t
   outside the range. The range form suffices for Lemma S2; the strong form is used only for
   the extra range in item 4.
4. *(C23)* holds for every node z of P_i ∩ P_a and every μ ∈ [max(x_a, y_a), i], where x_a and
   y_a are the indices of the ends of P_a. This interval contains [j_A, i] ⊇ [j_A, i1]. So any
   common node serves as the source of the overlap rule. Beyond i the equality is false in
   general (§10).
5. *(O3)* also holds for faces off P: a live annulus has at most one piece of each face off P.

**Taken from [18]** (details in §9): the structure of the recursion [18, Alg. 3], which sides
get a call and with which range, and the incision of P_i′ as a split of nodes
[18, Def. 2.2, Remark 2.5], used in the token form of Definition R and Lemma N. Neither
[18, Claim 2.3] nor F2, F4 or F5 of GHAT_REPAIR.md is used; the parts of them that are needed
are proved here.

## 1. Setting

The notation is that of RECURSION.md and GHAT_REPAIR.md (Definition R, the token graph,
Lemma N).

- G is a connected plane graph on the sphere S², P = p_0 … p_m is the shortest path of
  Theorem D, and e_k is the edge of G whose dual joins p_{k−1} and p_k. Lengths are
  w = K·c + 1. λ_t is the distance in A_1 from p_t^0 to p_t^1.
- At level ℓ the incised set is I_ℓ, with I_1 = E(P). A token, pair or edge is *old* at
  level ℓ if its edge is in I_ℓ, and *new* otherwise. Every old token is an end of its piece
  (GHAT_REPAIR.md, the token graph).
- A *P-piece* is a piece of a face of P. A piece of p_t^σ is a level-ℓ piece of the face p_t
  that refines the piece p_t^σ of A_1 (Lemma N, refinement part). Other pieces are *off P*.
- A *live annulus* of level ℓ is one on which ShortestCycle is called at depth ℓ. A_1 = G*_1
  is the only one of level 1.
- *Bounding paths.* A_1 has none. Let A be live and not a leaf, and Q the part it incises.
  The child on the low side (the j-side, range [j_A, i1]) has the j-bound of A and, as its
  k-bound, the copy of Q on the low side. The child on the high side (the k-side, range
  [i2, k_A]) has the copy of Q on the high side as its j-bound and the k-bound of A. We write
  P_a and P_b for the j-bound and the k-bound of A; either may be absent. A bound is the copy
  in A of the *incised part* of an ancestor's path, not of its whole path. [18] writes P_j and
  P_k for whole paths (Alg. 3, lines 9 to 12; Claim 2.3; Def. 2.8), so this is a reading (§9). The ends of P_a are
  a piece of p_{x_a}^0 and a piece of p_{y_a}^1 (Claim 14); those of P_b are a piece of
  p_{x_b}^0 and one of p_{y_b}^1. If P_a is absent, set x_a = y_a = 0; if P_b is absent, set
  x_b = y_b = m.
- *The step in A.* Let A be live, not a leaf, with range [j_A, k_A] and i = ⌊(j_A + k_A)/2⌋.
  P_i is a shortest path in A from A's piece of p_i^0 to A's piece of p_i^1 (both exist and
  are unique by (I3)), computed exactly and read from the 0-end. x is the index of the last
  0-piece on P_i and y the index of the first 1-piece after it. Q = P_i′ is the part of P_i
  between them, from a piece g_x of p_x^0 to a piece g_y of p_y^1. i1 and i2 are the least
  and greatest index of a P-piece on P_i. Since g_x and g_y are P-pieces on P_i,
  i1 ≤ min(x, y) and max(x, y) ≤ i2; this is all Lemma O uses. (Lemma S1(b) gives
  i1 = min(i, x, y) and i2 = max(i, x, y), but Lemma O does not need it.)
- *Q.* Q is a subpath of a shortest path, so it is a simple path and a shortest path between
  any two of its nodes. Its internal nodes are off P, by the choice of x and y. None of its
  edges is a copy of an edge of P: such a copy joins two pieces on the same side of γ, while
  an edge of Q has an end off P or joins a 0-piece to a 1-piece.
- *Incision in token form.* The level-(ℓ+1) cuts in the pieces of A are its level-ℓ cuts and
  one cut inside each dart of each new edge of Q. Another annulus A″ of the same level cuts only
  darts in its own pieces: a new edge of its incised part has its only pair in A″, and A″ is a
  component (I0), so no piece of A holds such a dart. A^Q is the graph whose nodes are the
  level-(ℓ+1) pieces that refine pieces of A and whose edges are the level-(ℓ+1) pairs of the
  edges that have a pair in A. The *subgraphs obtained by incising Q* are the components of
  A^Q. Nodes of A off Q do not change, and old pairs do not change. A new edge of Q gets two
  pairs, {(δ,1), (rev δ,2)} and {(δ,2), (rev δ,1)}. This is the incision of
  [18, Remark 2.5] in the reading of Lemma N and of sim/thmD.
- *Calls.* Following [18, Alg. 3] as read in RECURSION.md: if P_i meets P_a (shares a node with
  it; by (I4) the nodes of P_a ∪ P_b are exactly the nodes of A that carry an old token of an edge
  off P, so each node knows locally whether it lies on a bound), the j-side gets no call and the overlap rule of [18, Alg. 3, lines 9 to 14] computes,
  from a common node, a path for every t ∈ [j_A, i]. The k-side and P_b are symmetric. A side
  without overlap is called if its range is not empty. Overlap is tested directly, as P_i ∩ P_a ≠
  ∅, and not through the bad edges of [18, Claim 5.8], whose converse fails (GHAT_REPAIR.md, F3).
  Both rules, no call on an overlap side and no call on an empty range, are readings (§9). Claim 11 shows that such a side is one
  subgraph, so the call is well defined.

## 2. The curve model

### 2.1 Conventions

All curves are polygonal for a fixed piecewise linear structure on S², and the drawing of G
is polygonal. "Arc" means a simple curve with two distinct ends. A *Jordan domain* is a
component of the complement of a simple closed curve. We use four standard facts.
- **T1 (Jordan).** A simple closed curve J splits S² \ J into two connected open sets, each
  with boundary J. A connected set disjoint from J lies in one of them.
- **T2 (θ-curve).** Let D be a Jordan domain with boundary curve ∂D, and let κ be an arc with
  distinct ends on ∂D and interior in D. Then D \ κ has two components. Each is a Jordan
  domain bounded by κ and one of the two arcs of ∂D between the ends of κ.
- **T3 (parity).** Two closed curves in general position cross an even number of times.
- **T4 (one crossing).** If a curve crosses a simple closed curve J transversally at one
  point and meets J nowhere else, its two ends lie on different sides of J. A short segment
  that crosses J once in this way joins points on different sides.

Every Jordan domain with polygonal boundary can be crossed: two distinct points of its
boundary are joined by an arc whose interior lies in the domain.

### 2.2 The thickened drawing

Replace each vertex v of G by a small closed disc B_v and each edge e by a thin closed strip
S_e that joins the discs of its ends. The union N(G) of these sets is a regular neighbourhood
of G. Each face h of G becomes a component h° of S² \ N(G). Since G is connected, h° is an open
disc and ∂h° is a simple closed curve, also when the boundary walk of h repeats vertices or
edges. ∂h° follows the walk of h: one *side segment* of ∂S_e for each dart δ of h, and one
*corner arc* of ∂B_v for each corner. Boundaries of distinct faces are disjoint.

- A token (δ, 0) is the side segment of δ. For an incised dart δ, the *cut point* c(δ) is the
  midpoint of its side segment, (δ,1) is the half before c(δ) in walk order and (δ,2) the half
  after it. For a token τ of an incised dart δ, c(τ) = c(δ). The corner cuts c*_s and c*_t are
  points of the corner arcs of these corners.
- For an incised edge e with darts δ and rev δ, the *cut line* cl(e) is a segment across S_e
  from c(δ) to c(rev δ). The pair {(δ,1), (rev δ,2)} consists of the two halves at tail(δ),
  and the pair {(δ,2), (rev δ,1)} of the two halves at head(δ). So the two pairs of an incised
  edge lie in the two halves of S_e \ cl(e).
- The *arc* arc(g) of a piece g is the closed sub-arc of ∂h° made of the segments and halves
  of its tokens, the corner arcs between consecutive tokens, and, for a piece next to c*_s or
  c*_t, the part of the corner arc up to that corner cut; for a cyclic piece it is ∂h°. Its ends are cut points. Arcs of distinct
  pieces meet at most in their ends.

### 2.3 The arc γ

γ is the arc of Lemma N, drawn as follows. It starts at c*_s, runs through p_0° to c(e_1),
along cl(e_1), through p_1° to c(e_2), and so on, and ends through p_m° at c*_t. Its part
γ_t in p_t° is an arc from its *entry* (c*_s, or c(e_t)) to its *exit* (c(e_{t+1}), or c*_t)
with interior in p_t°. γ is simple because P visits each face once. We orient γ from c*_s
to c*_t and say that a point of γ *precedes* another.

γ has two local sides, and σ = 0 is the side of the piece p_0^0. By T2, γ_t splits the closed
disc of p_t into two *halves*; the σ-half H_t^σ is bounded by γ_t and arc(p_t^σ). For a
level-ℓ piece g of p_t^σ, the *low end* of arc(g) is its end nearer the entry of γ_t along
arc(p_t^σ), and the other end is the *high end*. The pair of e_k on side σ joins p_{k−1}^σ
and p_k^σ, because its two halves lie on one side of cl(e_k) ⊂ γ.

### 2.4 Incision curves, slots, collars and drawings

Every incision of a path Q in a live annulus adds a curve C_Q (Claim 3). K_ℓ is the union of
γ and of the curves of all incisions made at levels below ℓ, in all annuli. So K_1 = γ.

- A *chord* of K_ℓ in a face h is an arc of some C_Q whose interior lies in h° and whose ends
  are cut points on ∂h° or points of γ. K_ℓ meets the closed disc of h in its chords and, if h
  is a face of P, in γ_t. It meets a strip S_e in cl(e) if e ∈ I_ℓ and not at all otherwise.
- The *slot* Δ(g) of a piece g of a live annulus is the component of h° \ K_ℓ that contains
  the points of h° near the interior of arc(g). (K_ℓ meets ∂h° only in cut points, so such
  points exist and lie in one component.)
- A *collar* col(g) is a thin closed band in Δ(g) along arc(g) minus small neighbourhoods of
  its ends (all of ∂h° if g is cyclic).
- The *pair curve* of a pair π with tokens in pieces g and g′ runs from col(g) across the strip
  of its edge to col(g′): anywhere across the strip if the edge is new, and inside the half of
  S_e \ cl(e) that holds π if the edge is old. It enters the collars only near the middle of
  its two token segments.
- The *drawing* Γ(W) of a walk W is the union of the collars of its nodes and the pair curves
  of its edges. It is connected and avoids K_ℓ. Inside it, a curve runs from any point of the
  collar of the first node to any point of the collar of the last node. The drawing of a
  subgraph is defined the same way.

**Claim 1.** Let W and W′ be walks in a live annulus A that have no common node. Then Γ(W) ∩ Γ(W′) = ∅.

*Proof.* Collars of distinct pieces are disjoint: in distinct faces they lie in distinct
discs, and in one face they lie along arcs that meet at most in their ends, which collars
avoid. A pair curve meets only the collars of its own two pieces. W and W′ have no common
pair, since a common pair would give a common node. Pair curves of distinct edges lie in
distinct strips. The two pairs of one old edge lie in the two halves of S_e \ cl(e). ∎

## 3. The invariant

A live annulus A of level ℓ satisfies **(I)** if the following hold.

- **(I0)** A is a component of G*_ℓ.
- **(I1) Geometry.**
  (a) If g is a piece of A off P that is cyclic, Δ(g) = h°. If g is off P and linear, Δ(g) is
  a Jordan domain bounded by arc(g) and one chord of K_ℓ that joins the two ends of arc(g).
  (b) If g is a piece of p_t^σ, Δ(g) is a Jordan domain whose boundary consists of arc(g), a
  sub-arc γ_t[r_lo, r_hi] with r_lo ≠ r_hi (the *γ-part* of g), and up to two chords: one from
  the low end of arc(g) to r_lo and one from the high end to r_hi. A chord is absent where the
  end of arc(g) is the entry or exit of γ_t, which is then r_lo or r_hi.
  (c) There is a component Ω_A of S² \ K_ℓ that contains the slots of all pieces of A and, for
  every pair of A, the part of its strip on its side of the cut line (the whole open strip if
  its edge is new). Distinct live annuli of level ℓ have distinct such components.
  (d) If P_a exists, it was created by an incision whose curve C_a contains cl(e) for every
  edge e of P_a and runs from a point q_0^a of γ_{x_a}, which it reaches from the 0-side, to a
  point q_1^a of γ_{y_a}, which it reaches from the 1-side. J_a = C_a ∪ γ[q_0^a, q_1^a] is a
  simple closed curve, and Ω_A ⊂ Hi(J_a). Symmetrically for P_b, with C_b, q_0^b, q_1^b, J_b,
  and Ω_A ⊂ Lo(J_b). (Lo and Hi are defined in Claim 4.)
- **(I2) Bounding paths.** P_a is a path in A from A's piece of p_{x_a}^0 to A's piece of
  p_{y_a}^1, its internal nodes are off P, and the cut points of its first and last token are
  the low ends of the arcs of these two pieces. P_b is the same with high ends. P_a and P_b
  have no common node.
- **(I3) Pieces.** A has at most one piece of each face off P and at most one piece of each
  p_t^σ. It has a piece of p_t^0 exactly for t ∈ [x_a, x_b] and a piece of p_t^1 exactly for
  t ∈ [y_a, y_b], and max(x_a, y_a) ≤ j_A ≤ k_A ≤ min(x_b, y_b). We write g_t^σ for A's piece
  of p_t^σ.
- **(I4) Old pairs.** Every old pair of A is a copy of an edge of P or a pair of P_a or of P_b.
  A has at most one pair of each old edge off P.
- **(I5) Distances.** For every t such that A has g_t^0 and g_t^1, their distance in A is λ_t.

**Claim 2.** A_1 satisfies (I).

*Proof.* (I0): A_1 = G*_1, connected by Lemma N (level 1, proved there without [18]).
(I1): K_1 = γ. A face off P has one cyclic piece and no chord, so Δ = h°. The slot of p_t^σ is
the open half H_t^σ, bounded by arc(p_t^σ) and γ_t, with no chord. S² \ γ is connected, so it
is Ω_{A_1}. There are no bounding paths. (I2) is empty. (I3): A_1 has one piece of each p_t^σ
and one of each other face, and [x_a, x_b] = [y_a, y_b] = [0, m] ⊇ [j, k] = [0, m]. (I4): the
old edges at level 1 are the edges of P. (I5) is the definition of λ_t. ∎

From here on, A is a live annulus of level ℓ that satisfies (I) and is not a leaf, and P_i,
x, y, Q, g_x, g_y, i1 and i2 are as in §1. ε_0 is the token of Q's first edge at g_x and
ε_1 the token of Q's last edge at g_y. For an internal node g of Q, u and w are its two
tokens on Q.

## 4. One incision

**Claim 3 (the curve of Q).** Draw:
- for each new edge e of Q, a cut line cl(e) across S_e (for an old edge, cl(e) is in K_ℓ);
- for each internal node g of Q, a chord ch(g) from c(u) to c(w) with interior in Δ(g);
- a chord ch(g_x) from c(ε_0) to a point q_0 inside the γ-part of g_x, with interior in
  Δ(g_x), and ch(g_y) from c(ε_1) to a point q_1 inside the γ-part of g_y, with interior in
  Δ(g_y). The last piece of ch(g_x) and of ch(g_y) is a straight segment perpendicular to γ.
  The points q_0 and q_1 are distinct and differ from the ends of all chords of K_ℓ, and the
  points q chosen by all annuli of one level are pairwise distinct.

Let C_Q be the union of these chords and of the cut lines of all edges of Q, and
J = J_Q = C_Q ∪ γ[q_0, q_1]. Then:
(a) the drawing is possible; C_Q is an arc from q_0 to q_1 with C_Q ∩ γ = {q_0, q_1}, and J
is a simple closed curve;
(b) C_Q lies in the closure of Ω_A;
(c) J meets a strip S_e only in cl(e), and only if e is an edge of Q or an edge of P whose cut
line lies in γ[q_0, q_1]. J meets the closed disc of a face h only in the chords of C_Q in h
(two if x = y and h = p_x, at most one otherwise), and in γ[q_0, q_1].

*Proof.* (a) For an internal node g, u ≠ w, and c(u), c(w) are distinct points of arc(g): the
midpoint of the segment of a new token lies inside arc(g), and the cut point of an old token,
which is an end of g, is an end of arc(g). By (I1), Δ(g) is a Jordan domain whose boundary
contains arc(g), so ch(g) exists. The same holds at g_x and g_y, whose γ-parts have interior
points by (I1b). The internal nodes of Q are distinct pieces off P, so by (I3) they lie in
distinct faces. g_x and g_y lie in faces of P, and in distinct halves if x = y. So the chords
lie in pairwise disjoint slots. The edges of Q are copies of distinct edges of G: a new edge
has one pair, an old edge has one pair in A by (I4), and Q is simple. So the cut lines lie in
distinct strips. A chord meets ∂h° only in its ends, and a cut line meets the face discs only
in its ends. Walking along Q, consecutive pieces of C_Q share one cut point. All these cut
points are distinct, since they belong to distinct darts. So C_Q is an arc. It meets γ only in
q_0 and q_1: the edges of Q are not edges of P, so their strips meet γ nowhere; the faces of
the internal nodes are off P; and the interiors of ch(g_x) and ch(g_y) lie in slots, which
avoid γ ⊂ K_ℓ.
(b) Slots of pieces of A lie in Ω_A, and so does the open strip of a new edge of Q (I1c). The
cut line of an old edge of Q bounds the half-strip of its pair in A, which lies in Ω_A. The
ends of the chords lie on the boundaries of their slots.
(c) follows from the construction. ∎

**Claim 4 (sides along γ).** Let Lo(J) be the side of J that contains the points of γ before
min(q_0, q_1), and Hi(J) the other side. Then:
(a) the points of γ after max(q_0, q_1) lie in Hi(J);
(b) for a point r of γ other than q_0, q_1 and the ends of chords, the points near r on the
0-side of γ lie in Lo(J) if r precedes q_0 and in Hi(J) if q_0 precedes r; the points near r
on the 1-side lie in Lo(J) if r precedes q_1 and in Hi(J) if q_1 precedes r.

*Proof.* Let N be a closed disc around γ, so thin that J ∩ N consists of γ[q_0, q_1], a final
straight segment of ch(g_x) that reaches q_0 from the 0-side, and a final straight segment of
ch(g_y) that reaches q_1 from the 1-side. Its boundary ∂N is a simple closed curve made of the
0-bank (parallel to γ on the 0-side), the 1-bank and two short end arcs around the ends of γ.
J crosses ∂N exactly twice, transversally: once on the 0-bank, by ch(g_x), and once on the
1-bank, by ch(g_y). So ∂N \ J has two arcs, E_s through the end arc at c*_s and E_t through
the end arc at c*_t, and by T4 they lie on different sides of J. Points of γ before
min(q_0, q_1) join E_s by short arcs inside N that miss J, and points of γ after
max(q_0, q_1) join E_t in the same way. This gives (a) and shows that E_s lies in Lo(J). For
(b), fix r and shrink N, if needed, so that its width is less than half the distance from r to
q_0 and to q_1; the sides of J do not depend on N. The final segments of ch(g_x) and ch(g_y)
are perpendicular to γ (Claim 3), so inside N they lie within the width of N from q_0 and q_1.
A point near r on the 0-side joins the 0-bank by a segment perpendicular to γ, which lies
within the width of N from r. So the segment misses γ and both final segments. The part of the 0-bank before the crossing with ch(g_x) lies in E_s and the part
after it in E_t. The 1-side is the same with q_1. ∎

The low side is the j-side and the high side the k-side. Claims 6 and 11 justify this name:
the low side holds the P-pieces with the small indices, and when it is called it gets
[j_A, i1].

**Claim 5 ((O1), every subgraph on one side).** Draw A^Q with collars inside the slots of
level ℓ and outside C_Q, and with pair curves as in §2.4 for the incised set I_{ℓ+1}. This
drawing is disjoint from J. Hence the drawing of each component of A^Q lies in Lo(J) or in
Hi(J), and we say that the component, its pieces and its pairs lie on that side.

*Proof.* Let g′ be a piece of A^Q that refines the piece g of A. If g is not a node of Q, no
part of C_Q lies in Δ(g) (Claim 3c), and Δ(g) misses γ. If g is a node of Q, J meets Δ(g)
only in the interior of ch(g) (Δ(g) misses γ), and ch(g) meets ∂h° only in its ends on ∂h°.
These ends are ends of the arcs of the parts of g: a new cut point is where g splits, and an old cut point is an end of arc(g).
So a collar along the interior of arc(g′) can be chosen in Δ(g) \ ch(g). A pair curve lies in
its strip away from the cut line, and enters collars only near the middle of token segments,
away from chords; by Claim 3c it misses J. The drawing of a component is connected, so T1
applies. ∎

**Claim 6 ((O1), P-pieces and the ends of Q).**
(a) For t ≠ x, g_t^0 lies in Lo(J) if t < x and in Hi(J) if t > x. For t ≠ y, g_t^1 lies in
Lo(J) if t < y and in Hi(J) if t > y.
(b) If ε_0 is new, g_x splits at c(ε_0) into two pieces; the one whose arc runs from the low
end of arc(g_x) to c(ε_0) lies in Lo(J), the other in Hi(J). If ε_0 is old, g_x does not
change; it lies in Hi(J) if c(ε_0) is the low end of arc(g_x) and in Lo(J) if it is the high
end. The same holds for g_y, ε_1 and q_1.
(c) If ε_0 is old, its pair is the first edge of P_a or of P_b, and g_x is the first node of
that path. On P_a, g_x lies in Hi(J); on P_b, in Lo(J). If ε_1 is old, its pair is the last
edge of P_a or of P_b; on P_a, g_y lies in Hi(J); on P_b, in Lo(J).

*Proof.* (a) For t ≠ x, g_t^0 is not a node of Q, since Q's only 0-piece is g_x. So it does not
change, and Δ(g_t^0) is disjoint from J: it misses γ, and the chords of C_Q lie in the closures
of the slots of the nodes of Q, which are other slots (Claim 3c). By (I1b) its boundary contains a γ-part in
γ_t with interior points, so Δ(g_t^0) contains points on the 0-side near interior points r of
γ_t. All of γ_t precedes q_0 ∈ γ_x if t < x and follows it if t > x. Claim 4b gives the side.
The 1-pieces are the same with y and q_1.
(b) Write ∂Δ(g_x) as in (I1b): the arc-part from its low end to its high end, then the chord
to r_hi (or nothing), then γ_x back from r_hi to r_lo, then the chord to the low end (or
nothing). ch(g_x) joins c(ε_0) on the arc-part to q_0 inside the γ-part. By T2, Δ(g_x) \
ch(g_x) has two components: Δ_lo, bounded by ch(g_x), the arc-part from its low end to c(ε_0),
the old chord from the low end to r_lo if present, and the γ-part from r_lo to q_0; and Δ_hi,
bounded by ch(g_x), the arc-part from c(ε_0) to its high end, the old chord from the high end to
r_hi if present, and the γ-part from q_0 to r_hi. Both miss J (Claim 3c) and are connected. Δ_lo
contains points on the 0-side near points of γ_x before q_0, so it lies in Lo(J); Δ_hi lies in
Hi(J) for the same reason. If ε_0 is new, the collar of each part of g_x lies in the component
along its arc. If ε_0 is old, c(ε_0) is an end of arc(g_x), and all of arc(g_x) is on the
boundary of Δ_hi if it is the low end, or of Δ_lo if it is the high end.
(c) ε_0 is old, so by (I4) its pair is a copy of an edge of P or a pair of P_a or P_b. It is
not a copy of an edge of P (§1). Say it is a pair of P_a. Then g_x is a node of P_a, and the
only 0-piece on P_a is its first node (I2). So the pair is the first edge of P_a and ε_0 is
its first token, whose cut point is the low end of arc(g_x) by (I2). Now apply (b). On P_b the
cut point is the high end. At g_y the only 1-piece on a bounding path is its last node, and
(I2) gives the low end on P_a and the high end on P_b. ∎

**Claim 7 (local parity).**
(a) If cl(e) ⊂ J, the two halves of S_e \ cl(e) lie on different sides of J. In particular,
the two pairs of a new edge of Q lie on different sides.
(b) If a node g of Q is cut at a new cut point c, the two parts of g that meet at c lie on
different sides of J.

*Proof.* (a) A short segment in S_e that crosses cl(e) once meets J nowhere else (Claim 3c);
apply T4. (b) Near c, ch(g) leaves ∂h° into Δ(g) and separates the ends of the two collars
near c. A short arc near c joins them, crosses ch(g) once and meets J nowhere else; apply T4. ∎

**Claim 8 (the bounding paths).** Suppose P_a exists. Then:
(a) q_0^a precedes q_0 and q_1^a precedes q_1, and Lo(J_a) ⊂ Lo(J);
(b) A's pair of an edge of P_a that is not on Q lies in Lo(J), and so does every node of P_a
that is not on Q;
(c) A's pair of an edge of P_a that is on Q lies in Hi(J).
Symmetrically, if P_b exists: q_0 precedes q_0^b, q_1 precedes q_1^b, Hi(J_b) ⊂ Hi(J), the
pairs and nodes of P_b off Q lie in Hi(J), and A's pair of an edge of P_b on Q lies in Lo(J).

*Proof.* (a) Δ(g_x) lies in Ω_A ⊂ Hi(J_a) (I1c, I1d) and contains points on the 0-side near
q_0. By Claim 4b for J_a, these points lie in Lo(J_a) if q_0 precedes q_0^a. Hence q_0^a
precedes q_0; the 1-side is the same. Now J ∩ Lo(J_a) = ∅: C_Q lies in the closure of Ω_A,
which lies in Hi(J_a) ∪ J_a; and γ[q_0, q_1] lies after min(q_0^a, q_1^a), where γ is either
on J_a (between q_0^a and q_1^a) or in Hi(J_a) (after both, Claim 4a for J_a). Lo(J_a) is
connected, so it lies on one side of J. It contains the points of γ before
min(q_0^a, q_1^a), which precede min(q_0, q_1) and so lie in Lo(J).
(b), (c) Let e be an edge of P_a. By (I1d), cl(e) ⊂ J_a, so by Claim 7a for J_a the half of
S_e \ cl(e) opposite to A's pair lies in Lo(J_a), and hence in Lo(J). If e is not on Q, S_e
misses J (Claim 3c; e is not an edge of P, since a pair of P_a has an end off P or joins a
0-piece to a 1-piece), so A's pair lies in Lo(J) too. If e is on Q, cl(e) ⊂ J, and by Claim 7a A's pair lies on the other
side, Hi(J). A node of P_a that is not on Q is unchanged; its collar meets the pair curve of
an edge of P_a at it, which is not on Q, so it lies in Lo(J) as well.
P_b is the mirror image, with Hi(J_b) ⊂ Hi(J). ∎

**Claim 9 (nodes and edges of Q).** Suppose Q has no node of P_b. Then every node of Q has
exactly one part in Hi(J), and every edge of Q has exactly one pair in A^Q that lies in Hi(J).
The high parts and high pairs form a path Q^Hi from a piece of p_x^0 to a piece of p_y^1.
Symmetrically, if Q has no node of P_a, the same holds with Lo(J), giving Q^Lo.

*Proof.* *Edges.* A new edge has two pairs, on different sides (Claim 7a). An old edge of Q is,
by (I4), a pair of P_a or P_b; P_b is excluded, since its ends would be nodes of P_b. A has one
pair of it (I4), and that pair lies in Hi(J) (Claim 8c).
*Internal nodes.* Let g be an internal node of Q, in the face h.
- *g cyclic.* Its face has no cut, so u and w are new. g splits at c(u) and c(w) into two
  parts that meet at both points, and by Claim 7b they lie on different sides.
- *g linear.* Its end tokens are old: the cuts at its ends are dart cuts, since corner cuts
  lie in faces of P. By (I4) their pairs are pairs of P_a or P_b, since g is off P. Neither is
  on P_b, since g is not a node of P_b. So g is a node of P_a, and an internal one (I2). P_a
  has two distinct old tokens at g, which are ends of g, so they are its first token x_1 and
  its last token x_r, and r ≥ 2. Let u come before w in g. If u = x_1 and w = x_r, both edges
  of Q at g are edges of P_a, no new cut lies in g, and g lies in Hi(J) because the pair of u
  does (Claim 8c) and its curve meets col(g). Otherwise g splits into S_in, from u to w, and
  one or two pieces of S_out: the run from x_1 to the cut in u if u ≠ x_1, and the run from the
  cut in w to x_r if w ≠ x_r. A token of S_out among x_1, x_r belongs to an edge of P_a that
  is not on P_i, since P_i meets g only in u and w. By Claim 8b each piece of S_out lies in
  Lo(J). If u ≠ x_1, u is not an end of g, so it is new, and S_in meets a piece of S_out at the
  new cut point c(u); by Claim 7b, S_in lies in Hi(J). If u = x_1, then w ≠ x_r, and the same
  holds at c(w).
*Ends.* If ε_0 is new, g_x has one part on each side (Claim 6b). If ε_0 is old, its pair is on
P_a (not P_b) and g_x lies in Hi(J) as a whole (Claim 6c). The same holds at g_y.
*Path.* The high pair of an edge of Q has its pair curve in Hi(J), and that curve meets the
collars of the parts that hold its tokens, so these parts are the high parts of the two ends.
The high parts are distinct pieces, so Q^Hi is a path. Its first node is a part of g_x, a
piece of p_x^0, and its last node a part of g_y. ∎

**Claim 10 ((O1), separation at level ℓ).** Let t lie strictly between x and y, and suppose A
has g_t^0 and g_t^1. Then every walk in A from g_t^0 to g_t^1 meets a node of Q.

*Proof.* Let W be such a walk with no node on Q. Then its nodes and pairs do not change, W is a
walk in A^Q, and its drawing is connected and misses J (Claim 5). If x < t < y, g_t^0 lies in
Hi(J) and g_t^1 in Lo(J) (Claim 6a). If y < t < x, it is the other way round. Either way W
joins the two sides, a contradiction. ∎

**Claim 11 ((O2), the called side).** Suppose P_i has no node of P_b. Then:
(a) every component of A^Q contains a part of a node of Q;
(b) the high side is one subgraph A′, and A′ contains Q^Hi, so it holds exactly one pair of
each edge of Q;
(c) A′ has no bad edge: no edge of P_a or P_b that is not on P_i and has an end on P_i ∩ P_a or
P_i ∩ P_b;
(d) a bad edge in a subgraph of the j-side is an edge of P_a.
Symmetrically, if P_i has no node of P_a, the low side is one subgraph that contains Q^Lo, has
no bad edge, and holds one pair of each edge of Q; a bad edge on the k-side is an edge of P_b.

*Proof.* (a) Let C be a component of A^Q and v a node of C. If v is not a part of a node of Q,
v is a node of A off Q. A is connected (I0), so let R be a shortest path in A from v to a node
of Q. Its nodes before the last are off Q, so R minus its last node is a walk in A^Q, and its
last pair, which has an end off Q, is a pair of A^Q that joins it to a part of the last node.
(b) By (a) and Claim 9, every component on the high side contains the high part of some node
of Q. All high parts lie on the connected path Q^Hi. So there is one component on the high
side, and it contains Q^Hi. Its pairs of edges of Q are those of Q^Hi, one per edge, since the
other pair of each new edge is low (Claim 9).
(c) P_i has no node of P_b, so there is no bad edge of P_b. A bad edge of P_a is an edge of P_a
not on P_i, so not on Q, and by Claim 8b it lies in Lo(J).
(d) An edge of P_b that is not on P_i is not on Q, so it lies in Hi(J) by Claim 8. ∎

(a) and (d) hold without the hypothesis on P_b. When P_i meets P_a, the low side may consist of
several subgraphs (§10); it gets no call.

**Claim 12 ((O3) for the children).** Every called child A′ of A has at most one piece of each
p_t^σ and of each face off P. It has a piece of p_t^0 exactly for t ∈ [x, x_b] and a piece of
p_t^1 exactly for t ∈ [y, y_b] if it is the high side; for t ∈ [x_a, x] and t ∈ [y_a, y] if
it is the low side.

*Proof.* Take the high side; the low side is symmetric. P_i has no node of P_b. By refinement
(Lemma N), each piece of A′ refines a piece of A, and A has at most one piece of each kind
(I3). A piece of A off Q does not change. A node of Q has exactly one part in Hi(J)
(Claim 9), and A′ lies in Hi(J). So A′ has at most one piece of each kind. The 0-pieces of A
are the g_t^0 with t ∈ [x_a, x_b] (I3), and x lies in this interval since g_x is one. Those
with t > x lie in Hi(J) (Claim 6a) and in A′ (Claim 11b). g_x has a high part (Claim 9), which
lies on Q^Hi ⊂ A′. Those with t < x lie in Lo(J). The 1-pieces are the same with y. ∎

Since the soundness half of Lemma S2 reads a computed path between A's pieces of p_t^0 and
p_t^1, it uses (O3), which is (I3) for every live annulus (Claim 14).

**Claim 13 ((INV) for the called side, strong form).** Suppose P_i has no node of P_b, and let
A′ be the high side. If A′ has a piece of p_t^0 and a piece of p_t^1, their distance in A′ is
λ_t. The low side is symmetric.

*Proof.* (≥) By Lemma N (refinement), pieces of A′ refine pieces of A_1 and pairs are copies of
edges of the same length, so a walk in A′ maps to a walk in A_1 from p_t^0 to p_t^1 of the
same length, which is at least λ_t.

(≤) A′'s pieces of p_t^0 and p_t^1 refine g_t^0 and g_t^1, so by (I5) A has a walk W from g_t^0
to g_t^1 of length λ_t. For a node v of A, let φ(v) = v if v is off Q, and the high part of v
if v is on Q (Claim 9). For an edge of Q, let φ be its high pair.
- If W has no node on Q, it is a walk in A^Q that misses J, and it contains g_t^0, which is
  unchanged and is A′'s piece of p_t^0. So W lies in A′.
- Otherwise let p1 be the first and p2 the last position of W at a node of Q, with nodes z1
  and z2, and split W = W1·W2·W3 at p1 and p2. Let R be the part of Q between z1 and z2 (a
  single node if z1 = z2). R is a shortest path in A, so W′ = W1·R·W3 has length at most λ_t.
- *Lifting W1.* If p1 > 0, the nodes of W1 before z1 are off Q, and its pairs have an end off
  Q, so W1 minus z1 is a walk in A^Q that misses J and contains g_t^0 ∈ A′. Hence it lies in
  A′. Its last pair joins a node of A′ to a part of z1, so that part lies in A′ ⊂ Hi(J) and is
  φ(z1), the only high part of z1. If p1 = 0, then g_t^0 = z1 is a 0-piece on Q, so t = x and
  z1 = g_x, and φ(g_x) is A′'s piece of p_x^0 (Claim 12). W3 is the same at the other end; if
  p2 is the last position, t = y and φ(g_y) is A′'s piece of p_y^1.
- φ(R) is the part of Q^Hi between φ(z1) and φ(z2), a path in A′ of the same length.
So φ(W′), with the ends of W1 and W3 replaced by φ(z1) and φ(z2), is a walk in A′ between its
pieces of p_t^0 and p_t^1, of length at most λ_t. ∎

This covers the cases of the referee's third point. If t = i2 = x or i2 = y, the new walk
starts or ends with Q^Hi. If W meets Q in one node, R is that node, and both W1 and W3 attach
to its unique high part. The proof uses that the called side holds exactly one part of every
node of Q, which fails on a side with overlap.

**Claim 14 (the invariant passes on).** Every called child of A satisfies (I).

*Proof.* Take the high child A′ (P_i has no node of P_b); the low child is symmetric. Its
bounds are P_a′ = Q^Hi and P_b′ = P_b, with x_a′ = x, y_a′ = y, and its range is [i2, k_A].

(I0) A^Q is a union of components of G*_{ℓ+1}: a level-(ℓ+1) pair with a token in a piece of
A^Q is a copy of an edge with a pair in A, and A is closed under pairs (I0 for A). A′ is one
component of A^Q (Claim 11b), so it is a component of G*_{ℓ+1}.

(I1) K_{ℓ+1} adds to K_ℓ the curves C_Q of all incisions of level ℓ. The curve of another
annulus A″ lies in the closure of Ω_{A″} (Claim 3b), which misses Ω_A (I1c). So the only new
chords in the slots of A's pieces are the chords of C_Q, and each lies in the slot of its own
node. Let g′ be a piece of A′ that refines g.
- If g is not on Q, Δ(g′) = Δ(g) and (I1a, b) carry over.
- If g is an internal node of Q, Δ(g′) is the component of Δ(g) \ ch(g) along arc(g′). If g
  is cyclic, by T2 it is bounded by arc(g′) and ch(g). If g is linear, it is bounded by
  arc(g) ∪ (one chord) before, and by T2 the component along S_in is bounded by arc(S_in),
  from c(u) to c(w), and ch(g). This includes the unchanged case u = x_1, w = x_r.
- If g = g_x, Δ(g′) is Δ_hi of Claim 6. Its boundary is the arc-part from c(ε_0) to the high
  end of arc(g_x) (all of arc(g_x) if ε_0 is old), the old chord at the high end (or none),
  the γ-part γ_x[q_0, r_hi] with q_0 ≠ r_hi, and the new chord ch(g_x) from c(ε_0) to q_0. So
  (I1b) holds with ch(g_x) as the low chord. g_y is the same.
For (I1c), the slots and half-strips of A′ lie in Ω_A and miss K_{ℓ+1}; A′ is connected, and a
slot and the half-strip of a pair at it are joined across the open token segment, which
misses K_{ℓ+1}. So they lie in one component Ω_{A′} of S² \ K_{ℓ+1}, and Ω_{A′} ⊂ Ω_A ∩ Hi(J),
since it is connected, misses K_ℓ ∪ J and meets Ω_A ∩ Hi(J). Two children of one annulus lie
on different sides of J; children of distinct annuli lie in the distinct sets Ω_A. (I1d): the
j-curve of A′ is C_Q, which contains the cut lines of all edges of Q and runs from q_0 ∈ γ_x
(reached from the 0-side) to q_1 ∈ γ_y (from the 1-side), and Ω_{A′} ⊂ Hi(J); the k-curve is
J_b, and Ω_{A′} ⊂ Ω_A ⊂ Lo(J_b).

(I2) Q^Hi is a path in A′ from A′'s piece of p_x^0 to A′'s piece of p_y^1 with internal nodes
off P (Claims 9, 11). If ε_0 is new, the high part of g_x has arc from c(ε_0) to the high end,
and the token of Q^Hi's first pair there is the half of ε_0's segment next to c(ε_0), so its
cut point is the low end. If ε_0 is old, it is the first token of P_a, at the low end of g_x
(Claim 6c), and g_x is unchanged. The same holds at g_y. P_b has no node on Q, so its nodes and
pairs are unchanged; they lie in Hi(J) (Claim 8) and hence in A′, and (I2) for P_b carries
over. Q^Hi and P_b have no common node because Q has none on P_b.

(I3) Claim 12 gives the pieces, with [x, x_b] and [y, y_b]. For the range,
max(x, y) ≤ i2 = j_{A′} and k_{A′} = k_A ≤ min(x_b, y_b).

(I4) The old pairs of A′ are: copies of edges of P; pairs of A of old edges, which are pairs of
P_a or P_b, where those of P_a off Q lie in Lo(J) (Claim 8b) and are not in A′, those of P_a
on Q lie on Q^Hi, and those of P_b are on P_b; and the high pairs of the new edges of Q, which
lie on Q^Hi. A′ has one pair of each edge of Q (Claim 11b) and at most one pair of every other
old edge off P, since A has.

(I5) is Claim 13. ∎

**Claim 15 ((C23)).** Suppose P_a exists and P_i meets P_a in a node z. Then for every
μ ∈ [max(x_a, y_a), i],

  d_A(g_μ^0, z) + d_A(z, g_μ^1) = λ_μ.

By (I3), [max(x_a, y_a), i] ⊇ [j_A, i] ⊇ [j_A, i1]. Every common node z works. Symmetrically,
if P_i meets P_b in z, the equality holds for every μ ∈ [i, min(x_b, y_b)].

*Proof.* For μ ∈ [max(x_a, y_a), i], A has g_μ^0 and g_μ^1 (I3), and their distance in A is λ_μ
(I5). The left side is at least λ_μ, since the two shortest paths form a walk from g_μ^0 to
g_μ^1. For μ = i, z lies on P_i, which has length λ_i, so equality holds. Let μ < i, and let W
be a shortest walk in A from g_μ^0 to g_μ^1, of length λ_μ.

*Step 1: W meets P_i[g_i^0 .. z].* Suppose not. Build a closed curve Z^0 from four parts.
- ζ: a curve in the drawing of P_i[g_i^0 .. z], from col(g_i^0) to col(z).
- The connector: from col(z) along the pair curve of a pair π of P_a at z, of the edge e, then
  inside the half-strip of π to a point of cl(e) ⊂ C_a.
- C_a, followed from that point backwards to q_0^a.
- The 0-run: from q_0^a forward along γ on the 0-side, at small distance, to a point r_i
  inside the γ-part of g_i^0, then into Δ(g_i^0) and to the start of ζ in col(g_i^0). The
  γ-part of g_i^0 follows q_0^a, because Δ(g_i^0) ⊂ Hi(J_a) (Claim 4b for J_a).
Build a second closed curve: a curve ω in Γ(W) from col(g_μ^0) to col(g_μ^1), closed by an arc
β in the face p_μ. β runs inside the half H_μ^0 from col(g_μ^0) to a point near γ_μ on the
0-side, crosses γ_μ once at a point q, and runs inside H_μ^1 to col(g_μ^1). Choose q inside
γ_μ after q_0^a if μ = x_a and after q_1^a if μ = y_a. This is possible: if μ = x_a, the
chord of C_a in H_μ^0 splits it (T2) into a part before and a part after q_0^a, and Δ(g_μ^0)
lies in the part after, since g_μ^0 lies in Hi(J_a); so β avoids that chord. The same holds in
H_μ^1 if μ = y_a. The parts of β outside a thin neighbourhood of γ avoid it.

Now count crossings.
- ω and ζ: W and P_i[g_i^0 .. z] have no common node, so their drawings are disjoint
  (Claim 1).
- ω and the connector: W does not visit z, so it does not use π, and A has no other pair of e
  (I4). So ω misses col(z) and S_e.
- ω and C_a: ω lies in Ω_A, which misses K_ℓ ⊃ C_a.
- ω and the 0-run: collars avoid small neighbourhoods of cut points, and pair curves of edges
  of P cross their strips away from γ, so ω misses a thin neighbourhood of γ. In Δ(g_i^0),
  the run meets only the collar of g_i^0, which W does not visit.
- β and ζ, β and the connector: inside p_μ, A has only the pieces g_μ^0 and g_μ^1 (I3), and
  P_i[g_i^0 .. z] visits neither, since W would meet it; z is neither, for the same reason.
- β and C_a: the parts of C_a in p_μ are its chords at the ends of P_a, if μ = x_a or μ = y_a,
  and β avoids them.
- β and the 0-run: β crosses γ once, at q, and the run passes q on the 0-side, because
  q_0^a precedes q (μ > x_a, or the choice of q if μ = x_a) and q precedes r_i (μ < i). So β
  crosses the run exactly once.
So the closed curves ω ∪ β and Z^0 cross exactly once, against T3.

*Step 2: W meets P_i[z .. g_i^1].* Build Z^1 in the same way from the drawing of
P_i[z .. g_i^1], the 1-run on the 1-side from q_1^a forward to the γ-part of g_i^1, C_a from
q_1^a backwards to cl(e), and the connector at z. The same count, with q after q_1^a if
μ = y_a, gives exactly one crossing.

*Step 3: exchange.* Let v1 be a node of W on P_i[g_i^0 .. z] and v2 one on P_i[z .. g_i^1].
Replace the part of W between its visits to v1 and v2 (in whichever order W makes them) by the
part of P_i between v1 and v2, read in the same direction. That part passes through z, and,
as a subpath of the shortest path P_i, it is no longer than the part it replaces. So there is
a walk from g_μ^0 to g_μ^1 through z of length at most λ_μ, and the left side is at most λ_μ.

For P_b, mirror the construction: the runs go from the face p_i forward to q_0^b and q_1^b, and
need μ ≤ x_b and μ ≤ y_b. ∎

*Use in the overlap rule.* Lines 9 to 14 of [18, Alg. 3] grow a tree in A from a common node z
and read, for every t ∈ [j_A, i], the tree path between g_t^0 and g_t^1. It is a walk in A
between them, so its length is at least λ_t, and it is at most
d_A(g_t^0, z) + d_A(z, g_t^1) = λ_t. So the rule computes exactly λ_t for every t ∈ [j_A, i],
which is more than Lemma S2 needs ([j_A, i1]).

## 5. Lemma O, as proved

Let A be a live annulus of level ℓ that is not a leaf and satisfies (I) (A_1 does, Claim 2;
every called child does, Claim 14). Let P_i, x, y, Q, i1, i2 and J = J_Q be as above.

- **(O1)** Every subgraph obtained by incising Q lies on one side of J (Claim 5). A's pieces of
  p_t^0 for t < x and of p_t^1 for t < y lie on the low side; those with t > x and t > y on
  the high side (Claim 6a). At the end g_x: if Q's edge there is new, g_x splits into its part
  below the cut, on the low side, and its part above it, on the high side. If the edge is old,
  it is the first edge of P_a or of P_b, g_x does not split, and it lies on the high side if
  the edge is on P_a and on the low side if it is on P_b. The same holds at g_y with the last
  edge (Claim 6b, c). In the old case P_i meets that bounding path at g_x, so that side gets no
  call, and the called side, if any, holds all of g_x. For t strictly between x and y with both
  pieces in A, every walk in A from g_t^0 to g_t^1 meets a node of Q (Claim 10).
- **(O2)** A side on which P_i does not meet the bounding path is one subgraph; it has no bad
  edge and holds exactly one copy of each edge of Q. A bad edge in a subgraph of the j-side is
  an edge of P_a; on the k-side, of P_b (Claim 11).
- **(O3)** Every live annulus has at most one piece of each p_t^σ and of each face off P
  ((I3), Claims 2, 12, 14).
- **(INV)** For every live annulus A and every t such that A has pieces of p_t^0 and p_t^1, in
  particular every t ∈ [j_A, k_A], their distance in A is λ_t ((I5), Claims 2, 13).
- **(C23)** If P_i meets P_a in z, then d_A(g_μ^0, z) + d_A(z, g_μ^1) = λ_μ for every
  μ ∈ [max(x_a, y_a), i] ⊇ [j_A, i]. Symmetrically for P_b and μ ∈ [i, min(x_b, y_b)]
  (Claim 15).

The facts (P), (B), (W), (S_1) and Lemma S1 of RECURSION.md are not used, so Lemma O does not
depend on RECURSION.md.

## 6. Degenerate cases

- *x = y.* g_x and g_y are the two pieces of A in the face p_x, in different halves. q_0 and
  q_1 lie in γ_x, in either order; Claim 4 does not depend on the order. Claim 10 is empty.
- *t = x or t = y.* The end pieces are treated by Claim 6b, c; in Claim 13 the walk W then
  starts or ends on Q, and the lift starts or ends at the high part.
- *Q of length 1.* C_Q = ch(g_x) ∪ cl(e) ∪ ch(g_y). If the edge is old, it is the first edge of
  P_a (or P_b) at g_x and its last edge at g_y, so the bounding path is this single edge and Q
  equals it.
- *Q along P_a or P_b.* Old edges of Q are edges of P_a or P_b (I4); internal nodes of Q that
  are linear lie on P_a or P_b (Claim 9). J then shares cut lines, and possibly ends of chords,
  with J_a or J_b; Claims 3 and 8 allow this. If Q runs along P_a through a node with both
  tokens old, the node does not change and lies on the high side (Claim 9).
- *Q equal to P_a.* All of Q lies on the high side, the low side is empty (Claim 11a: every
  subgraph contains a part of a node of Q), the j-side overlaps, and the k-side child is A
  itself with the range [i2, k_A] and the same bounds.
- *Copies of P outside the range.* (I3) records all P-pieces of A, also those with index
  outside [j_A, k_A]; Claims 6 and 12 hold for all indices, and Claim 15 reaches below j_A.
- *The cuts at s and t.* The low end of arc(p_0^σ) is c*_s, the entry of γ_0, and the high
  end of arc(p_m^σ) is c*_t. Chords of incision curves end at midpoints of side segments of
  edges off P, never at c*_s or c*_t. The endpoint data of R0 (mode, moved token) change Ĝ_ℓ,
  not the token graph, so they do not enter.
- *m = 0 or m = 1.* A_1 is a leaf and no incision happens.
- *Bridges, loops, deg(s) = 1, parallel edges.* The thickened drawing gives every dart its own
  side segment, so a bridge with one face on both sides has two segments in that face, and a
  corner arc of a vertex of degree 1 runs around the end of its strip. Nothing else changes.
- *An end piece of one old token.* It cannot occur in a non-leaf annulus. A cut lies inside an
  incised dart or at c*_s or c*_t, so a piece made of one old token has c*_s or c*_t as an end of
  its arc and lies in p_0 or p_m. In p_0, c*_s is the entry of γ_0, so the token's cut point is
  the high end, and by Claim 6c, (I2) and (I4) its pair lies on P_b with this piece as an end.
  Then x_b = 0 or y_b = 0, so k_A ≤ 0 by (I3), and A is a leaf. In p_m the mirror argument puts
  the pair on P_a, so j_A ≥ m. The referee's flag for this case never fired in 177,000 runs.
- *A without P_a or P_b.* The claims about the missing path are empty; with x_a = y_a = 0 or
  x_b = y_b = m, (I3) still holds. At level 1 all internal nodes of Q are cyclic and both ends
  split.

## 7. The six gap points of the referee

1. *Jordan separation.* The sides are the sides of the simple closed curve J_Q (Claim 3).
   Claims 4, 5 and 10 give (O1) and (S) at level ℓ from T1 and T4.
2. *Old end edges.* Claim 6b, c gives the rule; an old end edge lies on P_a or P_b, the end does
   not split and goes to the side away from that path, and that path's side overlaps.
3. *(INV) at junctions and single touches.* Claim 13, using that the called side holds exactly
   one part of each node of Q (Claim 9), which holds because the called side has no overlap.
4. *[18, Claim 2.3].* Claim 15 proves the form used here, for any common node and a larger
   range, with the parity argument of (S_1) on the region bounded by P_i[g_i^0 .. z], the
   bounding curve and the 0-copy side of γ.
5. *Sidedness of bad edges.* Claim 8 and Claim 11c, d.
6. *(O3) for soundness.* Claim 12 and (I3).

## 8. The proof of (S_1)

The proof of (S_1) in RECURSION.md is correct. Points that its words leave implicit:
- The curves inside pieces should be drawn in collars, so that W's curve misses a thin
  neighbourhood of γ; then its crossings of P's edges are away from γ, as stated.
- "Since W and Q̄ share no node, the two curves are disjoint" also needs that the two copies of
  an edge of P cross its strip at different ends (§2.2), and that two pieces of one face in
  A_1 lie in different halves.
- W may visit p_x^1 or p_y^0. The closing run of Q̄ crosses γ inside p_x within the thin
  neighbourhood and enters the 0-half of p_x only to reach the collar of p_x^0, which W does
  not visit; likewise at p_y. So the run still misses W's curve.
- Q̄ visits no piece of p_t, since t differs from x and y and Q̄ has no copy of P inside; so
  W's closing arc in p_t misses Q̄'s curve.
- T3 holds for closed curves that are not simple, so Q̄ may repeat nodes.
Claim 15 reuses this style. Claim 10 is the same fact at level ℓ for the incised part Q, with
the Jordan curve J_Q in place of a parity count.

## 9. What comes from [18], and what does not

*Taken from [18].*
- [18, Alg. 3]: in a live annulus that is not a leaf, P_i is computed for the middle index, its
  part P_i′ is incised, the overlap rule of lines 9 to 14 runs on a side where P_i meets the
  bounding path, and the two sides are called with the ranges [j, i1] and [i2, k].

*Readings and choices.* Three points are ours, not [18]'s.
- *The bounding path is the incised copy.* [18] tests P_i ∩ P_j ≠ ∅ for the whole path P_j
  (Alg. 3, lines 9 to 12; Claim 2.3; Def. 2.8). We read P_j as the copy in A of the parent's
  incised part P_i′, which is the bound P_a. Two reasons: only under this reading does the
  bad-edge rule of [18, Claim 5.8] make sense, since with whole paths the copies of edges of P on
  the parts outside P_i′ would count as bad edges; and the test is local, since by (I4) the nodes
  of P_a ∪ P_b are exactly those that carry an old token of an edge off P. The two readings
  differ: the parent's whole path U·Q·V often has U and V inside the child, and P_i can meet
  them off the copy. In the referee's runs (§12), 1,561 sides of 162,000 instances overlapped
  only under the whole-path reading. A driver with the whole-path test (sim/thmD/refereeO,
  thmD_F.py) gave the right value on all 84,000 of its instances, and (C23) held at all 108,059
  checks at common nodes off the copy, but Claim 15 does not cover those nodes, so the
  whole-path reading is unproved.
- *No call on an overlap side.* This follows [18, Def. 2.8]. [18]'s implementation decides by
  bad edges instead ([18, Claim 5.8]), and the converse of Claim 5.8 fails (GHAT_REPAIR.md, F3),
  so Theorem D tests overlap directly. A called overlap side could break (I2), since P_a and Q^Lo
  would meet.
- *No call on an empty range.* [18, Alg. 3, line 18] calls the side with range [j, i1] even when
  i1 < j; its leaf branch would then look for a piece of p_j^0 that the side need not have
  (Claim 12).
Both call rules only remove calls, so Lemma S2 is unaffected by them.
- [18, Def. 2.2, Remark 2.5]: incising a path splits its nodes and doubles its new edges. We
  use this in the token form of Definition R and Lemma N, in which the level-(ℓ+1) pieces are
  the runs between cuts, and we identify the two sides A_l and A_r of [18] with the low and the
  high side. This identification is a reading, also made by Lemma N and sim/thmD.

*Proved here, although [18] or F1 to F5 state it.*
- Internal nodes of P_i′ that an earlier incision split lie on P_a or P_b, and old edges of P_i′
  lie on P_a or P_b (F1, F2): from (I4), in Claims 6c and 9.
- Live annuli are connected and are components of G*_ℓ (F4, Lemma N): (I0), Claim 11.
- [18, Claim 2.3] in the form used: Claim 15.
- Which side a discarded part lies on (the direction of [18, Claim 5.8] used in F3): Claim 11c,
  d. The converse of [18, Claim 5.8] is not used.

*Not used.* [18, Lemma 2.6] (F5), [18, Claims 2.4, 2.10, 2.12], and the cases of Lemma N's
proof that rely on F2 and F3.

## 10. Tests

Scripts in sim/thmD/lemmaO: patchO.py writes thmD_O.py, a copy of sim/thmD/thmD.py with checks
at every incision and at every child (`python3 -I patchO.py ../thmD.py thmD_O.py`; the driver is
read, not changed); runO.py runs
instances with opts = {mode 'claimed', variant 'fixed', pairs 1, pcommon, pfar, e0rule
'formal', ends 1}; lanes.sh, lanes2.sh and lanes3.sh run the lanes. Each lane runs two
processes under alarm 1800 with python -I.

Checks at each incision, in A before the incision:
- (I2): kinds of the ends of P_a and P_b, internal nodes off P, cut point of the first and last
  token at the low end (P_a) or high end (P_b), simple paths, no common node;
- (I3): at most one piece per (t, σ), the exact index intervals, the range inequalities;
- (I4): every old pair is a copy of an edge of P or on P_a or P_b; at most one pair per old
  edge off P;
- (I5) in the strong form, for every t with both pieces (lanes E, F);
- (O1): the predicted side of every P-piece (Claim 6a), of both end pieces by the cut position
  of the end token (Claim 6b, c), of the pairs and nodes of P_a and P_b off Q and on Q
  (Claim 8), of the two pairs of every new edge of Q (Claim 7a), of the two parts at every new
  cut of a cyclic node, and of S_in and S_out at every linear internal node (Claim 9); no
  component of A^Q mixes predicted sides; every component contains a part of a node of Q;
- (O2) on each side without overlap: one component, one part of each node of Q, one pair of
  each edge of Q, no bad edge; bad edges only on the side of their path;
- (C23): for every common node z of P_i and a bounding path and every m with both pieces in A,
  sorted by where m lies;
- (INV) at every called child, for every t in its range.

Results (lanes A and B ran before the end-rule check used the cut position, which they checked
by token order; lanes C to F use the cut position):

| lane | instances | family | incisions | failed checks |
|---|---|---|---|---|
| A | 150,000 | default, tie-break random | 90,667 | 0 |
| B | 25,000 | up to 70 vertices, grid 12, pcommon 0.15, pfar 0.7, tie-break minid | 27,628 | 0 |
| C | 80,000 | as A | 48,196 | 0 |
| D | 15,000 | as B | 16,932 | 0 |
| E | 60,000 | as A, with (I5) strong | 36,102 | 0 |
| F | 12,000 | as B, with (I5) strong | 13,343 | 0 |

In total 342,000 instances and 232,868 incisions, with no failed check. Coverage over all
lanes:
- x = y in 72,697 incisions, and Q of length 1 in 67,718;
- 73,301 linear internal nodes of Q: 59,071 unchanged (Q runs along a bounding path through
  them) and 14,230 split (12,692 into S_in and one piece of S_out, 1,538 into S_in and two);
- 47,323 end pieces with an old end token on P_a and 24,871 on P_b, each on the predicted side;
- 130,394 old edges of Q on P_a and 72,634 on P_b;
- 417,577 sides without overlap, each one subgraph; 48,159 sides with overlap, of which 2,888
  consisted of several subgraphs (they get no call);
- 7,765 incisions in annuli with both bounding paths;
- (INV) at children: 818,830 checks; (I5) in the strong form (lanes E, F): 195,118 indices in
  the range and 10,829 outside it.

(C23) by the position of m, all lanes, for 150,448 common nodes z on 48,159 sides with
overlap. The equality was tested against λ_m and against d_A(g_m^0, g_m^1), with the same
counts, since the two agree by (I5).

| μ in (j-side; the k-side is the mirror) | checks | equality fails |
|---|---|---|
| [max(x_a, y_a), j_A) | 95,047 | 0 |
| [j_A, i] | 320,774 | 0 |
| (i, i2] | 12,044 | 1,669 |
| beyond i2 | 184,078 | 84,996 |

So the range of Claim 15 cannot be extended past i in general. Lemma S2 needs [j_A, i1].

## 11. Points of doubt

- T1 to T4 and the polygonal setting are used without proof. They are standard, and only
  simple closed curves, cross-cuts of Jordan domains and transversal crossings occur.
- The identification of [18]'s incision and its two sides with the token form and the low and
  high side of J_Q is a reading (§9). If [18] meant a different incision, Lemma N would fail
  too.
- The invariant (I) has many parts, and each is used: (I0) in Claims 11 and 14, (I1) for the
  curves, (I2) for the end rule, (I3) for disjoint slots and (O3), (I4) for old edges and
  linear nodes, (I5) for (INV) and (C23). An error in one would break the induction; the tests
  check each part at every incision.
- The bounding path is read as the incised copy (§9); the whole-path reading of [18] passed
  the tests but is not proved.

## 12. Referee pass (2026-10-29)

Verdict: correct with minor gaps; no fatal or serious error. The referee checked Claims 1 to 15,
(I) for A_1 and its passage to called children (also when several annuli of one level incise at
once), and that Lemma O supplies what Lemma S2 uses. The minor points, all fixed above:
- M1, M2: the bounding path as the incised copy, and the two call rules, are readings, not taken
  from [18] (§1, §9).
- M3: Claim 4(b) chose N before r; now the final chord segments are perpendicular to γ and N is
  shrunk for each r (Claims 3, 4).
- M4: arc(g) includes the corner arcs (§2.2).
- M5: Claim 6(b) listed the old chords on the boundaries of Δ_lo and Δ_hi.
- M6: Claim 3(c) has two chords in p_x when x = y.
- M7: incision in token form speaks of the pieces of A, not its faces, and says why another
  annulus of the same level does not cut them (§1).
- M8: the points q of one level are pairwise distinct (Claim 3).
- M9: Lemma O no longer cites Lemma S1(b) (§1, §5).
- M10: the end piece of one old token cannot occur (§6), replacing a point of doubt.
- M11: the running index of Claim 15 is μ, since m is the last index of P; Claim 1 does not need
  (I3).
- M12, M13: NOTES.md §5 and Lemma S2 in RECURSION.md.

Referee tests (sim/thmD/refereeO; patchR.py turns lemmaO/thmD_O.py into thmD_R.py; lanesR.sh,
lanesF.sh, runHits.py): 162,000 instances in seven lanes R1 to R7 with 118,856 incisions, among
them three lanes with every legal corner and mode of R0 (anycorner), and the 25 saved instances of
the adversarial search in 15,000 runs. No failed check. Totals: 420,268 checks of (INV) at
children, 172,652 of (C23) on [j_A, i], 39,976 linear internal nodes of Q (717 split into three),
4,515 incisions with both bounds. F1 to F3 (84,000 instances) ran the whole-path overlap test of
§9 and gave no wrong value.
