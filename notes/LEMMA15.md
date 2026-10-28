# Repairing [1, Lemma 15] (and the part of [1, Lemma 16] that Theorem A uses)

Theorem A needs the labels (L) of [1]. For every bag X, every v ∈ X learns d̃_X(v,h) and
d̃_X(h,v) for all h ∈ ∂S⁺_X, with dist_{G[X]} ≤ d̃_X ≤ (1+ε)·dist_{G[X]}, in Õ(D/ε) rounds.
[1] builds them with Lemma 15 (oracles for the cut-open bags O_X) and Lemma 16 (labels). Both
proofs have gaps.

This file splits the repair into two layers:
- **The topological layer (§3).** [1] supplies it through Def. 6 and Lemma 14, but Lemma 14
  is false as stated (§2, (S7)). §3 replaces both with a different construction. Its pieces
  are *tiles*: the faces of a growing set of corners of G. §3 proves the interface,
  Lemma 14′, that the analytic layer needs.
- **The analytic layer (§4 to §7).** Error recursion, LP, rounding, gluing and labels, proved
  from Lemma 14′.

Status (2026-10-28):
- The first draft was refereed and attacked. Both passes confirmed the analytic layer, and
  both found that its topological black box, [1, Lemma 14], fails.
- §3 is new in this revision and is checked numerically (§3.7).
- **Referee pass on §3.** Given its black box, §3 is correct. The pass raised one serious
  point and several minor ones, all fixed here.
  - **The serious point.** The child shape assumed before, one child per outside component,
    contradicts 7(a).
  - **The fix.** §1 now uses the shape of [8]'s construction: outside components grouped,
    and contiguity at each separator vertex. The label-change bound becomes 8|S_A|.
- **Adversarial pass on §3.** It ran on the draft before the referee's fixes and broke
  nothing in §3 under that draft's assumptions (§3.7). Its two findings against the
  assumptions are the referee's points again, and the fixes above remove both.
  - With one child per outside component, (G1′) and 7(a) leave a child with n − 2 vertices
    on stars, so no BDD of height O(log n) has that shape. With [8]'s grouping the same
    search finds children of at most n/2 + 1 vertices.
  - A chord fan puts 2k − 2 label changes on one vertex. That breaks the old bound of 4 per
    vertex, but not 4 + 2c_s.
- **Still open.** No adversarial pass has seen the fixed text, and no human has checked §3.
  Until then Theorem A, and everything built on it, stays conditional on Lemma 14′.

## 1. What we take from [1]

Notation is that of [1, Sec. 5]:
- **The decomposition tree.** Its height is H = O(log n). h(X) is the height of bag X (leaves
  have height 0), and d(X) its depth (the root has depth 0).
- **Per bag X:**
  - T_X: a spanning tree of G[X] with diameter O(D log n). [8, Sec. 4.2, Step 1] builds it
    from T[X] plus O(log n) edges. [1, Lemma 9] states the stronger Property 4, that T[X]
    itself is a spanning tree of height O(D), but [8, Def. 4.1 (6)] only gives O(log n)
    components for T[X]. We use T_X, which costs one log factor in sizes and rounds.
  - S_X: the separator, a simple cycle made of a path q_X of T_X with at least one edge and
    one closing edge, which may be virtual and is then drawn inside a face of G[X]
    [8, Thm 4.4]. |S_X| = O(D log n).
  - ∂S*_X = ⋃ over proper ancestors A of S_A ∩ X, and ∂S⁺_X = ∂S*_X ∪ S_X;
    |∂S⁺_X| = O(D log² n).
  - c_X: the centre.

The following are used as black boxes.

- **(G1) Decomposition** [1, Lemma 9], as built by [8, Sec. 4.2]. We use Properties 1 to 3
  and 5 to 7 of [1], T_X in place of Property 4, and the child shape of [8, Sec. 4.2].
  [1, Sec. 5.1.1] describes that shape loosely as "one child per component". [9, Sec. 5]
  describes it as one inside child plus outside children attached along subpaths S_i of S_X.
  We use it in this form:
  - **(G1′) Children.**
    - X_in consists of S_X and the vertices inside it ([8]'s X⁺).
    - Every vertex of X outside S_X lies in exactly one other child. Each other child is a
      union of components of G[X] − S_X lying outside S_X, together with vertices of S_X, and
      it contains the neighbours on S_X of each of its components.
    - **Contiguity.** At every s ∈ S_X there is a direction z_s in the outside wedge of s
      such that all edges from s to vertices outside S_X that lie on the same side of z_s go
      into one child.
  - **Why [8] gives this.** [8]'s outside children are the components of an auxiliary graph
    on S_X and the outside vertices.
    - In that graph, a separator vertex s on the boundary of the bag's region is split into
      two copies, at the direction z_s that points out of the region. The edges on either
      side of z_s go to different copies. An unsplit vertex keeps all its edges.
    - The one child that is disconnected without the virtual edge is split into its two
      components.
    - A vertex outside S_X has all its edges in the auxiliary graph, which gives the second
      item. The splitting rule gives contiguity.
    - So s lies in X_in and in at most two outside children, which is 7(a).

  Two consequences that [1] uses without stating them:
  - **(7c′)** if x ∈ X_i ∖ S_X and xt ∈ E(G[X]), then t ∈ X_i. An inside x has only inside
    and separator neighbours. An outside x shares a component with its outside neighbours,
    and its separator neighbours are in that component's child.
  - **(7c)** every edge of G[X] lies in G[X_i] for some child X_i, since S_X ⊆ X_in. This is
    [8, Def. 4.1 (3)].

  Properties 7(a) and 7(b) imply neither.
  - **Adversarial check.** (7c) and (7c′) held in 300 of 300 instances.
  - **One child per component, inside included.** Children of the form C ∪ (S_X ∩ N(C))
    for every component C break (7c) in 118 of 300 instances: a separator edge uw, with u
    next to only C₁ and w next to only C₂, lies in no child. §3 needs X_in ⊇ S_X.
  - **One child per outside component.** This reading contradicts 7(a). With pendant leaves
    in every corner, one separator vertex touches up to 37 outside components (referee,
    `sim/ref2/pendant.py`). [8]'s grouping avoids this.
- **(G3) Realization** [10, Thm 1] (refereed, SODA 2025).
  - **Claim.** Let d be a quasimetric on T and σ a cyclic order on T. Suppose d satisfies
    the cyclic Monge condition (M) below for σ. Then some plane digraph K with O(|T|⁶)
    vertices and nonnegative weights realizes d exactly on T and is disk-drawn with T in
    order σ (§3.1).
  - **Same condition.** [10, Thm 1] asks that D(t₁,t₃) + D(t₂,t₄) ≥ D(t₁,t₄) + D(t₂,t₃) for
    all quadruples appearing in σ in this order. Read over the four rotations of a circular
    quadruple, this is exactly (M) in its four orientations.
  - **The order is prescribed.** [10, Thm 1] takes σ as given. This closes the gap in
    [1, Thm 2], whose statement promises a prescribed order but whose proof does not show
    it.
  - **Computing K.** CONGEST does not charge for local computation. So c_X can find K by
    exhaustive search over plane digraphs with O(|T|⁶) vertices, solving an LP for the
    weights each time. A rational d gives rational weights.
  - **Polynomial local time.** If that is wanted, [1, Thm 2] is the candidate, but only
    after its order guarantee has been checked. Nothing below needs it.
- **(G4) Monge.** Let a plane digraph be disk-drawn with terminal set T in order σ, with
  finite terminal distances. Then the distances satisfy (M) for σ.

  (M) reads: for all terminals a, b, c, d in this cyclic order, and for each of the four
  orientations (u,v) ∈ {(a,c),(c,a)}, (w,z) ∈ {(b,d),(d,b)},
  δ(u,z) + δ(w,v) ≤ δ(u,v) + δ(w,z).

  The proof: a u to v path and a w to z path must cross at some vertex x, and splitting both
  at x gives the inequality. (M) is (13) of [1] imposed for every cyclic rotation of σ. [1]
  imposes (13) only for one linear reading of σ, which is weaker. The referee's LP check
  (`sim/ref/monge.py`) shows the difference matters: it finds a d that satisfies (13),
  the triangle inequalities and 1 ≤ d ≤ 100 on four terminals, yet violates (1) of [1] by
  149.5.
- **(G5) Oracle** [1, Lemma 11]. A plane digraph with integer weights in [0, N] has a
  (1+ε)-approximate distance oracle that never underestimates. Its labels have Õ(log N / ε)
  words per vertex; the Õ(1/ε) of [1] is the case N = poly(n).
- **(G6) Face identifiers** [9, Lemma 5.11]. In Õ(D) rounds the faces of G get distinct
  O(log n)-bit IDs, and every vertex learns, for each of its corners, the ID of the face that
  contains it.

Two assumptions on the graph the oracle runs on. Both hold for every call in Theorem A:
- **(W1) Weights.** Every weight is an integer in [1, W], with W = poly(n).
  - Why it holds: the discretized Alg. 1 (NOTES, Assembly; `Boost.lean`) runs every oracle
    call on ℓ_i + η, and Run.len_nonneg gives ℓ_i + η ≥ η.
  - Round each such length up to a multiple of η/n and divide by η/n. The result is an
    integer in [n, poly(n)].
  - The rounding never shortens a walk and stretches it by a factor of at most 1+1/n, which
    the budget 1+ε₀ with ε₀ = Θ(1/log n) absorbs.
  - Weight 0, which (R) by itself would allow, never reaches the oracle.
- **(W2) Both directions.** Every network edge carries arcs in both directions; missing
  directions get weight M₂ (NOTES, "Infinite distances"). So a connected piece is strongly
  connected, and its terminal distances are finite.

## 2. The gaps in [1]

- **(S1) Wrong reference in step 2.** [1, Thm 2] minimizes distortion relative to its input,
  the oracle values δ_i, not relative to O_{X_i}.
  - If the witness is O_{X_i}, as the text suggests, the minimum distortion can be
    (1+ε′)^i. The output is then only known to be within (1+ε′)^{2i} of O_{X_i}.
  - The exponent then follows e_h = 2e_{h−1} + 1 and reaches about 2^H = poly(n) at the root.
    Holding that to 1+ε forces ε′ = ε/poly(n), and the labels no longer have size Õ(D/ε).
  - The adversarial pass built a star instance with γ = 0.1, where α* = 1.1 and an optimal LP
    point sits at ratio 1.21 = (1+γ)² from O.
  - The intended bound does hold, but only with the witness of Lemma R5.
- **(S2) No triangle constraints, and no quasimetric input.**
  - The LP (13) to (15) of [1, Thm 2] has no triangle inequalities, so its solution need not
    be a quasimetric, and (G3) does not apply to it.
  - The input to Thm 2, the oracle answers, need not be a quasimetric either.
- **(S3) Bit size.** LP solutions are rationals of large bit size, and oracle labels grow
  with log N.
- **(S4) Steps 3 and 4 are not proved.**
  - Step 3 claims that the glued H_X is "planar" and "aligned" (lty 1762-1767) without proof.
  - Step 4 cuts P_X open "in H_X", but the edges of P_X are not edges of H_X; they lie inside
    the K_{X_i}. Neither the cut nor the distortion claimed after it is defined or proved.
- **(S5) Infinite distances.** Directed G[X] and O_X can have unreachable terminal pairs.
  (G3), (G4) and the LP need finite values.
- **(S6) First separator vertex.** The proof of Lemma 16(b) assumes that the first vertex of
  S_X on a path from a non-hub v lies in v's child. This is true for [8]'s children,
  since the edge into S_X is drawn in the child's region. It is just not among Properties 1
  to 7. Def. 6 step 4 (lty 1530-1531) uses the same fact. We record it as (7c′).
- **(S7) [1, Lemma 14] is false as stated.** The claim is that cutting P_X open merges all
  holes of G[X] into one face carrying P_X ∪ ∂S*_X. The adversarial pass (scripts in
  `sim/attack/`) breaks it in three configurations, all consistent with Properties 1
  to 7 and [8]'s rule for children:
  1. **Separator chords** (`g2_chord_bfs.py`, `g2_chord.py`).
     - Setup: a non-tree edge between two separator vertices, drawn inside S. Its endpoints
       are on the boundary of the outside child, so the induced G[X] of that child contains
       the edge. The edge lies in the child's hole and splits it.
     - Effect: J lies on two faces.
     - Numbers: in 58 of 100 random weightings no cyclic order has α* = 1, and the worst
       instance needs α* = 1.636.
     - So the LP of step 2 is infeasible for every order, and (I1) already fails at a leaf.
       The referee found the same failure with the inside child and a chord drawn outside.
  2. **Virtual edges** (`g2_virtual.py`).
     - Setup: on a 13×8 grid, two nested separators close through virtual edges in the same
       face. Every ∂S*_X vertex is then already on one face of G[X], but Def. 6 step 3 still
       adds a connecting path, since the separators are vertex-disjoint.
     - Effect: cutting that path, both of whose ends lie on the same face, splits O_X into two
       components of 30 vertices. b is unreachable from a even with (W2), while
       dist_{G[X]}(a,b) = 20.
  3. **Holes that touch at one vertex** (`g2_pinch.py`).
     - Setup: S₁ ∩ S₂ = {u}. Then step 3 is skipped and P_X = ∅, so the two holes stay two
       faces.
     - Numbers: 53 of 60 weightings have no valid order; the worst needs α* = 1.727.

  A control run on 300 genuine one-face instances gave α* = 1 every time
  (`lp_sanity.py`), so the failures are not LP artefacts. The flaw in the proof is that it
  infers that faces merge from the fact that the cut paths form a connected tree. §3
  replaces Def. 6 and Lemma 14; §3.6 explains why none of the three configurations can occur
  there.
- **(S8) Smaller gaps.**
  - Def. 6 step 3 is undefined when P_X ∪ ∂S*_X = ∅, which is the case for the root's
    children.
  - The base case has an off-by-one: the leaf oracle gives 1+ε′, but the hypothesis states
    (1+ε′)^0 (lty 1742-1749).
  - The Monge constraints (13) cover one linear reading of σ only; see (G4).

## 3. Lemma 14′: tiles

### 3.1 Corners, the radial graph and tiles

G is connected and plane, n ≥ 2, and every vertex knows its rotation, as in [1].
r_v(0), …, r_v(deg v − 1) is the rotation at v, with indices taken mod deg v.

- **Corners.** The corner (v, j) is the angle at v between r_v(j−1) and r_v(j). It lies in
  one face of G.
- **The radial graph R.** Its vertex set is V(G) ∪ F(G), and it has one edge per corner,
  joining v to the face that contains the corner, drawn inside that angle.
  - R is a connected plane bipartite graph.
  - Its faces correspond one to one to the edges of G. The face R_e of e = uw is bounded by
    the corners next to e at u and at w, and e is drawn inside R_e. (Euler's formula checks
    the count: |V(R)| − |E(R)| + |E(G)| = n + |F(G)| − 2|E(G)| + |E(G)| = 2.)
- **Tiles.** Let Γ be a set of corners, read also as a subgraph of R. Two edges of G are
  *Γ-adjacent* if they are consecutive at some vertex and the corner between them is not in
  Γ. The *tiles* of Γ are the classes of the equivalence relation this generates.

**Fact 1.** The tiles of Γ correspond one to one to the faces of Γ. The face for a tile τ is
the union of the faces R_e with e ∈ τ, together with the R-edges and R-vertices outside Γ
that lie between them. We write τ for both.

*Proof.* A face of Γ is a component of S² ∖ Γ. It is a union of open faces R_e, open R-edges
outside Γ and R-vertices outside Γ. R_e and R_e′ share the R-edge (v, j) exactly when e and
e′ are r_v(j−1) and r_v(j). An R-vertex outside Γ has all its R-edges outside Γ, so the faces
around it are already joined through those R-edges. ∎

**Fact 2 (standard).** Let Γ be nonempty and connected, and let τ be a face of Γ.
- τ is an open disk.
- There is a closed disk D_τ with a continuous map π_τ : D_τ → S² that maps int D_τ
  homeomorphically onto τ and maps ∂D_τ onto ∂τ ⊆ Γ, following τ's boundary walk.
- A point of ∂τ has one preimage for each visit of the walk.

**Sectors and ports.** Let v ∈ V(Γ), that is, some corner at v lies in Γ.
- The corners of Γ at v cut v's rotation into *sectors*: maximal runs of consecutive edges
  with no corner of Γ between them. A sector is nonempty and lies in one tile.
- Each angle of Γ at v contains exactly one sector. So the sectors of v in τ correspond one
  to one to the visits of v by τ's boundary walk.
- The *opening corner* of a sector is the corner of Γ just before its first edge.
- If v ∉ V(Γ), all edges at v lie in one tile.

**Pieces.** The piece P_τ of a tile τ has:
- a vertex (v, s), called a *port*, for every v ∈ V(Γ) and every sector s of v in τ;
- a vertex v for every v ∉ V(Γ) with an edge in τ;
- for every edge e = uw in τ, an edge with e's arcs and weights. It joins the copy of u whose
  sector contains e (or u itself) to the copy of w whose sector contains e.

σ_τ is the cyclic order in which τ's boundary walk visits the ports. Each port is visited
once and has at least one edge. Identifying the copies of each vertex maps P_τ onto the
subgraph of G formed by the edges in τ.

**Disk-drawn.** A graph A is *disk-drawn with terminals T in order σ* if three things hold:
- A is drawn in a closed disk D;
- A meets ∂D exactly in T, each terminal at one point;
- the terminals appear along ∂D in the order σ.

This is what "T on the outer face in order σ" means in (G3), (G4) and Lemma R5. A vertex
outside D, joined to T in the order σ, keeps the drawing plane, and that is all the crossing
argument of (G4) uses.

**Fact 3.** If Γ is nonempty and connected, every piece P_τ is disk-drawn in D_τ with its
ports in order σ_τ. π_τ maps this drawing onto the edges of τ as drawn in G and sends (v, s)
to v.

*Proof.* An edge e in τ has its interior inside R_e ⊆ τ, so it lifts through π_τ uniquely.
- **Ends.** The end of e at u lifts to the visit of u through whose angle e leaves u, which
  is the port for the sector that contains e. If u ∉ V(Γ), it lifts to the unique preimage of
  u.
- **Plane.** Edges of G meet only at common ends, so the lift is a plane drawing.
- **Boundary.** It meets ∂D_τ only at lifted vertices of V(Γ), which are the ports. Each port
  sits at its own point, and they appear in the order of the walk. ∎

### 3.2 The construction

Labels and corner sets are defined level by level.

- **Labels.** λ_0(e) := root for every edge e. For d ≥ 0 and e = uw, let X := λ_d(e).
  - If X is a leaf, λ_{d+1}(e) := X.
  - Otherwise X is a non-leaf at depth d (by induction), and λ_{d+1}(e) is defined by the
    first rule that applies:
    1. the child of X that contains u, if u ∉ S_X;
    2. the child of X that contains w, if w ∉ S_X;
    3. X_in.
- **Rails.** The *rail* of an edge e = uw is the pair of corners next to e on one side: the
  corner at u between e and r_u(i+1), where e = r_u(i), and the corner at w between r_w(k−1)
  and e, where e = r_w(k). Both lie in the face f of G whose boundary walk contains the dart
  from u to w (with the turning rule that passes (w, k) on arrival at w). So the rail is an
  R-path u, f, w.
- **Corner sets.** Γ_0 := ∅, and Γ_{d+1} := Γ_d ∪ ⋃ N_X over the non-leaf bags X at depth d,
  where N_X := L_X ∪ Q_X ∪ P_X:
  - **L_X** is the set of corners at vertices of S_X whose two edges e, e′ satisfy
    λ_d(e) = λ_d(e′) = X and λ_{d+1}(e) ≠ λ_{d+1}(e′).
  - **Q_X** is the set of rails of the edges e of q_X with λ_d(e) = X.
  - **P_X** is empty unless three things hold: d ≥ 1, λ_d(e) = X for every edge e of q_X,
    and no vertex of q_X lies in V(Γ_d). In that case let p_X be a shortest path in T_X
    from V(q_X) to V(Γ_d) ∩ X. P_X is the set of rails of its edges. Claim 3 shows that every
    edge of p_X is labelled X.

If the root is a leaf there is nothing to do: [1]'s leaf step computes everything.
- **What a bag owns.** Let X be a bag at depth d ≥ 1.
  - Its *tiles* are the tiles of Γ_d on which λ_d ≡ X. Claim 2 shows that λ_d is constant
    on tiles.
  - O_X is the disjoint union of the pieces of its tiles, and J_X is the set of their ports.
  - Its *outside edges* are E^out_X := E(G[X]) ∖ λ_d^{-1}(X).
- **Gluing relations.** Let X be a non-leaf at depth d. Its *child tiles* are the tiles of
  Γ_{d+1} owned by children of X.
  - For a tile τ of X, ~_τ identifies two ports (v, s′) and (v, s″) of child tiles inside τ
    when s′ and s″ lie in the same sector of v with respect to Γ_d, or when v ∉ V(Γ_d).
  - ~_G identifies all ports of child tiles that are copies of one vertex, together with the
    ends of outside edges at that vertex.

Unlike Def. 6 of [1], nothing is ever cut: not along a separator edge, and not along a hub
path. The closing edge of S_X, real or virtual, is never used.

### 3.3 Lemma 14′

**Lemma 14′.** Assume (G1) and (W2). Then Γ_d is connected for every d ≥ 1. Moreover, the
following hold for every bag X at depth d ≥ 1, and (T4) holds for the root as well.
- **(T1) Labels.** λ_d is constant on every tile of Γ_d. If λ_d(e) = X, then
  e ∈ E(G[X]). Labels only move down the bag tree: λ_{d+1}(e) is λ_d(e) or a child of it.
- **(T2) Size.**
  - |N_A| = O(D log n) for every non-leaf A.
  - |J_X| ≤ Σ_{A ∈ Anc*(X)} |N_A| = O(D log² n).
  - If X is not a leaf, Σ_i |J_{X_i}| = O(D log² n) over its children X_i.
  - Every outside edge of X joins two vertices of ∂S*_X, so |E^out_X| ≤ 3|∂S*_X| =
    O(D log² n).
- **(T3) Disks.** The piece of every tile τ of X is disk-drawn in D_τ with its ports in
  order σ_τ.
- **(T4) Assembly.** Let X be a non-leaf. Every child tile lies inside one tile of X, and
  every edge of a tile of X lies in a child tile.
  - (a) Glue(child tile pieces, outside edges of X; ~_G) = G[X]. Here each outside edge is a
    piece of its own with both ends as terminals. Every vertex of ∂S⁺_X is a terminal image.
  - (b) For every tile τ of X, Glue(pieces of the child tiles inside τ; ~_τ) = P_τ, and
    every port of τ is a terminal image.
  - (c) Both gluings come from disk decompositions in the sense of Lemma R3.
    - For (b): the disks of the child tiles inside τ, mapped into D_τ, with ~_τ.
    - For (a): the disks of all tiles of Γ_{d+1}, mapped into S², with all copies of each
      vertex identified. That gluing is G. The child tiles of X and the outside edges of X
      (edges of other tiles) are parts of it.
- **(T5) Locality.**
  - Γ_{d+1} and λ_{d+1} are computed from Γ_d and λ_d in Õ(D) rounds, for all bags of depth
    d together. Afterwards every vertex knows which of its corners lie in Γ_{d+1} and the
    labels of its edges.
  - From O(|J_Y|) words, a centre c_Y computes σ_τ for every tile τ of Y.
  - From Õ(D) words, c_X computes ~_τ for each of its tiles, ~_G, which child tiles lie in
    which tile of X, and σ for every child tile.

Every component of a piece has a port. A component without one would consist of vertices
outside V(Γ), all of whose edges lie in the piece. It would then be closed under adjacency in
G, so it would be all of G. But Γ ≠ ∅ has a G-vertex, since R is bipartite.

### 3.4 Proofs

**Claim 1 (labels stay in the bag).** If λ_d(e) = X, then e ∈ E(G[X]). Moreover λ_{d+1}(e)
is λ_d(e) or a child of it, and a label other than a leaf has depth exactly d.

*Proof.* Induction on d. The case d = 0 is clear. Let X = λ_d(e) be a non-leaf, with
e = uw ∈ E(G[X]).
- If u ∉ S_X, then u lies in exactly one child Y by 7(a), and w ∈ Y by (7c′).
- If w ∉ S_X, the same holds with u and w swapped. When both rules apply, they give the same
  child, by (7c′).
- If u, w ∈ S_X, both lie in X_in ⊇ S_X by (G1′).

The rest is read off the definition. ∎

**Claim 2 (one label per tile).** For every d, λ_d is constant on every tile of Γ_d. Hence:
- (2a) if two edges at v have different labels λ_d, then v ∈ V(Γ_d);
- (2b) a corner of N_X that is not in Γ_d lies inside a tile of X, and both its edges have
  label X. So the sets N_X ∖ Γ_d of different bags at depth d are disjoint, and the tiles of
  a leaf never change after its depth.

*Proof.* Induction on d. Γ_0 = ∅ has one tile, labelled root. For the step, let e, e′ be
consecutive at v with corner c ∉ Γ_{d+1}. Then c ∉ Γ_d, so e, e′ lie in one tile of Γ_d, and
λ_d(e) = λ_d(e′) =: X by induction. If X is a leaf, nothing changes. Otherwise:
- If v ∉ S_X, both edges get the child that contains v (rules 1 and 2, with (7c′)).
- If v ∈ S_X, then λ_{d+1}(e) ≠ λ_{d+1}(e′) would put c in L_X ⊆ Γ_{d+1}, which is
  excluded.

So Γ_{d+1}-adjacent edges have equal labels λ_{d+1}.

For (2a), walk around v from one edge to the other. Some consecutive pair has different
labels, and its corner is in Γ_d.

For (2b):
- A corner of L_X has two edges labelled X.
- A rail corner of e lies between e and another edge e″ at the same vertex, with λ_d(e) = X.
  If the corner is not in Γ_d, then e″ is in e's tile.
- For the rails of P_X, this uses that every edge of p_X is labelled X. Claim 3 (step 3)
  shows this, using only Claim 2 at depth d, so there is no circularity.

New corners are added only by non-leaves, and only inside their own tiles. ∎

**Claim 3 (Γ_d is connected for d ≥ 1).**

*Proof.* We show three things:
- N_root is nonempty and connected;
- for every non-leaf X at depth d ≥ 1, every corner of N_X is joined to Γ_d inside
  Γ_d ∪ N_X;
- a non-leaf X at depth d with no edge labelled X has N_X = ∅.

Induction then gives the claim. Let q = q_X; it has at least one edge by (G1′).
1. **Rails of runs.** The rail of an edge of q is an R-path through both ends of that edge.
   So the rails of a run of consecutive X-labelled edges of q form a connected subgraph that
   contains all the vertices of the run.
2. **Some edge of q has another label.** This is impossible at d = 0, where every edge is
   labelled root. Each maximal run of X-labelled edges of q has an end vertex incident to an
   edge of q with another label. By (2a) that vertex is in V(Γ_d), so every component of Q_X
   meets Γ_d.
3. **Every edge of q is labelled X.** Then Q_X is connected and contains V(q).
   - If d = 0, or V(q) meets V(Γ_d), we are done.
   - Otherwise P_X is defined. No vertex of q is in V(Γ_d), so all edges at a vertex of q
     lie in one tile. Consecutive edges of q share a vertex, so q lies in one tile τ₀ of X.
   - **p_X exists.** τ₀ is a face of the nonempty graph Γ_d. Its boundary walk visits a
     G-vertex, since R is bipartite. That vertex is the end of an edge in τ₀, so it lies in
     X by Claim 1. So V(Γ_d) ∩ X ≠ ∅, and T_X is a spanning tree of G[X].
   - **p_X lies in τ₀.** Every vertex of p_X except the last is outside V(Γ_d), so all its
     edges lie in one tile. The first vertex is on q, so its tile is τ₀. Inductively, every
     edge of p_X lies in τ₀ and is labelled X.
   - So the rails of p_X form an R-path from Q_X to a vertex of V(Γ_d).
4. **L_X.** A corner of L_X at v ∈ V(q) has edges labelled X.
   - If v is an end of an X-labelled edge of q, then v ∈ V(Q_X).
   - Otherwise every edge of q at v has another label, and there is at least one such edge.
     So v ∈ V(Γ_d) by (2a).

If no edge is labelled X, then L_X and Q_X are empty by definition. P_X is empty too, since
the edges of q would have to be labelled X. ∎

So for d ≥ 1 every tile is an open disk, and Facts 2 and 3 apply. This proves (T3).

**Claim 4 (hubs lie on Γ).** Let A be a non-leaf at depth d_A, and let v ∈ S_A have an edge
e with λ_{d_A}(e) = A. Then v ∈ V(Γ_{d_A+1}).

As a consequence, let X be a bag at depth d and v ∈ ∂S⁺_X with an edge labelled X. Then
v ∈ V(Γ_{d+1}), and v ∈ V(Γ_d) if v ∈ ∂S*_X. To see this, apply the claim to the A ∈
Anc(X) with v ∈ S_A, using λ_{d_A}(e) = A from Claim 1.

*Proof.* If v is an end of an A-labelled edge of q_A, its rail is in Q_A. Otherwise every
edge of q_A at v has another label, and v has at least one such edge, while e is labelled A.
By (2a), v ∈ V(Γ_{d_A}). ∎

**Claim 5 (outside edges).** Every outside edge uw of X joins two vertices of ∂S*_X.

*Proof.* Let A be the deepest ancestor of X with λ_{d(A)}(uw) = A. It exists, since the root
qualifies, and A ≠ X. Let A′ be the child of A on the way to X.
- **u ∈ S_A.** Suppose u ∉ S_A. Then u ∈ X ⊆ A′, and rules 1 and 2 with (7c′) give
  λ_{d(A)+1}(uw) = A′, against the choice of A.
- **w ∈ S_A**, by the same argument.

So u, w ∈ S_A ∩ X ⊆ ∂S*_X. Outside edges form a simple plane graph on ∂S*_X, so there are at
most 3|∂S*_X| of them. ∎

**Claim 6 (assembly, (T4)).**

*Proof.* Let X be a non-leaf at depth d.
- **Child tiles lie in tiles of X.** Let τ′ be a tile of Γ_{d+1} owned by a child Y of X.
  Its edges have λ_d = X by Claim 1. Γ_{d+1}-adjacency implies Γ_d-adjacency, so τ′ lies
  in one tile of Γ_d, and that tile belongs to X. Every edge of a tile of X gets a child
  label, so it lies in a child tile.
- **(b).** A sector of v with respect to Γ_{d+1} lies inside one sector of v with respect to
  Γ_d.
  - Under ~_τ, a port (v, s′) of a child tile inside τ goes to (v, s), where s ⊇ s′ is its
    Γ_d-sector, which lies in τ. If v ∉ V(Γ_d), it goes to v.
  - A vertex v ∉ V(Γ_{d+1}) has one copy, which is not a terminal, and v ∉ V(Γ_d).
  - So the glued graph has the vertices of P_τ and the edges of τ with the right ends; it is
    P_τ.
  - **Ports are terminal images.** Take a port (v, s) of τ. The first edge of s lies in a
    child tile τ′, in a sector s′ ⊆ s. (v, s′) is a port of τ′, because
    v ∈ V(Γ_d) ⊆ V(Γ_{d+1}).
- **(a).** The edges of the glued graph are λ_d^{-1}(X) ∪ E^out_X = E(G[X]), by Claim 1.
  Take v ∈ X; it has an edge in G[X], since G[X] is connected (Property 3) and |X| ≥ 2.
  - If v ∈ V(Γ_{d+1}), all its copies in child tiles are ports, and ~_G merges them with the
    outside edge ends at v.
  - If v ∉ V(Γ_{d+1}) and v has an edge labelled X, then v has a single copy in one child
    tile. It is not the end of an outside edge: by Claim 5 such an end lies in ∂S*_X, and by
    Claim 4 it would then be in V(Γ_d).
  - If v has no edge labelled X, its copies are outside edge ends, all terminals.

  So the glued graph is G[X].
  - **∂S⁺_X vertices are terminal images.** If v ∈ ∂S⁺_X has an edge labelled X, Claim 4
    puts v in V(Γ_{d+1}), so all its copies are ports. Otherwise v is an outside edge end.
- **(c), for (b).** Lift Λ := Γ_{d+1} ∩ τ̄ to D_τ through π_τ.
  - A corner of N_X inside τ is an open R-edge in τ, so it lifts uniquely.
  - Λ̃ := ∂D_τ ∪ (lifted corners) is connected. A component of the new corners inside τ
    must reach Γ_d, because Γ_{d+1} is connected, and it can only leave τ through ∂τ.
  - The faces of Λ̃ are the lifts of the child tiles inside τ, since π_τ is a homeomorphism
    on the interior.
  - Composing their closure maps with π_τ gives the maps π_{τ′}. The lifted maps
    D_{τ′} → D_τ are injective on interiors, the interiors have disjoint images, and those
    images miss Λ̃ ⊇ ⋃ (images of ∂D_{τ′}).
  - Two ports have the same image in D_τ iff they are copies of v in the same Γ_d-sector,
    or v ∉ V(Γ_d), that is, iff they are ~_τ-equivalent.
  - A boundary point that is not a port maps to an F-vertex of R or into an R-edge, never to
    the image of a port.
- **(c), for (a).** Use the same maps π_{τ′} : D_{τ′} → S² for all tiles of Γ_{d+1}, with
  ~_G. For the root, Γ_1 plays this part. ∎

**Claim 7 (size, (T2)).**

*Proof.* Let A be a non-leaf at depth d_A.
- **|L_A| ≤ 8|S_A|.** Take s ∈ S_A and the edges at s labelled A, in rotation order.
  - **Wedges.** The two edges a, b of the cycle S_A at s split the rotation into an inside
    wedge and an outside wedge W. One of a, b may be virtual.
  - **Their new labels.**
    - Edges into the inside wedge, a and b themselves, and edges between separator vertices
      become A_in.
    - An edge from s to a vertex outside S_A lies in W. It becomes the outside child
      containing that vertex.
    - By contiguity in (G1′), the direction z_s splits W into W₁ and W₂ such that all such
      edges in W₁ go to one child O₁, and all those in W₂ go to one child O₂.
  - **Outside chords.** Let c_s be the number of edges at s between separator vertices that
    are drawn in W.
  - **Count at s.** In the cyclic sequence, the A_in edges form at most 1 + c_s maximal runs:
    the inside wedge with a and b, plus one run per outside chord. Each run causes at most
    two label changes. Apart from these, the label can change only from O₁ to O₂: once at
    z_s, and once more across the inside wedge if that wedge carries no A-labelled edge. So
    there are at most 4 + 2c_s label changes, and that many corners of L_A at s.
  - **Sum over s.** The outside chords of the cycle S_A are pairwise non-crossing. So there
    are at most |S_A| − 2 of them: the |S_A| − 3 diagonals of a polygon, plus possibly a real
    edge parallel to a virtual closing edge. Hence Σ_s c_s ≤ 2|S_A| and |L_A| ≤ 8|S_A|.
- **|N_A| = O(D log n).** |Q_A| ≤ 2|E(q_A)| and |P_A| ≤ 2|E(p_A)|. Both q_A and p_A are paths
  in T_A, whose diameter is O(D log n), and |S_A| = |V(q_A)|.
- **|J_X| ≤ Σ_{A ∈ Anc*(X)} |N_A|.** Map each port of X to the opening corner of its sector.
  This map is injective. The opening corner lies in Γ_d, so it was added by some bag A at
  depth d_A < d. By (2b), the first edge of the sector was labelled A at depth d_A, and it
  is labelled X at depth d. So A is an ancestor of X, by Claim 1.
- **Children.** The same map, from the ports of all children of X into Γ_{d+1}, gives
  Σ_i |J_{X_i}| ≤ Σ_{A ∈ Anc*(X) ∪ {X}} |N_A|.
- **Outside edges.** Claim 5. ∎

### 3.5 Locality, (T5)

**Building Γ_{d+1}.** All of this runs for all bags of depth d in parallel, with congestion 2
by Property 6, so a level takes Õ(D) rounds.
- **Labels.** Each end of e knows its bags (Property 2) and whether it lies in S_X. Once
  every centre has broadcast its parent's ID within its bag, it also knows which of its bags
  is the parent of which. So λ_{d+1} is computed locally.
- **L_X and Q_X** are computed locally.
- **P_X.** First, one aggregation over T_X decides whether every edge of q_X is labelled X
  and whether V(q_X) meets V(Γ_d). If P_X is needed, a BFS in T_X from V(q_X), stopped at
  V(Γ_d), finds p_X. This takes O(D log n) rounds.

**Contour ranks.** Root T at r and walk around it, passing corners by the turning rule of
face traversal restricted to T. Each corner is passed once, and its *rank* is its position in
this walk. Every vertex computes the ranks of its corners after one convergecast of corner
counts and one broadcast of offsets along T, which takes O(D) rounds.

**Rank lemma.** For every face f of G, the cyclic order of f's corners along its boundary
walk is their cyclic order by rank, with the same orientation for all faces.

*Proof.*
- **Cutting.** T is a spanning tree, so cutting S² along T leaves an open disk Δ whose
  boundary is the contour of T.
- **Blowing up.** Blow up each visit of a vertex to a short arc of ∂Δ. The corners then
  become disjoint subarcs of ∂Δ in rank order, and every non-tree edge becomes a chord with
  distinct ends.
- **Regions.** The chords are pairwise disjoint, and the faces of G are the regions of Δ that
  they cut out.
- **Induction on the chords.** A new chord inside a region ρ splits ρ's boundary cycle into
  two parts. Each part is a contiguous piece of ρ's cyclic sequence of arcs. So every region
  meets ∂Δ in arcs whose order along the region's boundary is their order along ∂Δ.
- **Orientation.** Every region lies inside Δ, so walking its boundary with the region on
  the left traverses these arcs in the direction of ∂Δ. ∎

**Orders.** Together with (G6), this gives the orders σ_τ. Let Y be a bag whose tiles are
faces of Γ.
- **What c_Y collects.** The two corners of Γ that bound each port of Y, each with its
  vertex, rotation index, rank and face ID. That is O(|J_Y|) words.
- **Walking.** The boundary walk of a tile τ leaves a port (v, s) through the corner of Γ
  that closes s, the one after the last edge of s. It enters the face f of that corner and
  continues with the next corner of Γ at f in rank order. The direction is the one in which
  the first boundary edges of f passed belong to τ. That corner is the opening corner of the
  next port. It is the closing corner itself when f has only one corner in Γ.
- **The next corner was collected.** The corners of f strictly between the two are not in Γ,
  so the edges of f's boundary between them lie in τ (Fact 1). So the next corner bounds a
  port of Y, and c_Y has it.

For the parent, c_X does the same with Γ_{d+1} and the corners that bound child ports. Each
port record also carries the Γ_d-sector of its port, which v knows locally. That gives ~_τ,
and vertex IDs give ~_G.

**Child tiles to tiles of X.** The child tiles inside one tile τ of X are exactly the classes
of the relation "adjacent across a corner of N_X ∖ Γ_d". These are the faces of the connected
graph Λ̃ in D_τ, and such faces are connected through shared edges. c_X sees each such corner
as the closing corner of one child port and the opening corner of the next.

All this is Õ(D) words per bag by (T2), and leaves need nothing beyond gathering G[L] as in
[1]. ∎

### 3.6 The three configurations of (S7)

1. **Chords.** A chord between separator vertices is labelled X_in and lies in a tile of
   X_in. Nothing is cut along it. An outside child that contains both ends sees it as an
   outside edge, which goes into H straight away (§5, step 5). The tiles of every child are
   disks by Claim 3 and Fact 2.
2. **Virtual edges.** These are never used. Γ consists of corners of G only, and
   connectivity comes from rails along edges of G.
3. **Pinches.** A vertex that a tile's boundary visits twice gives two ports, (v, s) and
   (v, s′), each once on the walk. The LP treats them as different terminals, and ~_τ and
   ~_G identify them again.

### 3.7 Numerical checks

Two prototypes in `sim/tiles/` build the construction literally:
- `sim/tiles/tiles2.py` follows the text. Its children are shaped as in [8]: X⁺, plus
  the components of the auxiliary graph, with z-directions inherited down the tree and the
  split at the virtual edge. p_X is a path in T_X, taken only when every edge of q_X is
  labelled X.
- `sim/tiles/tiles.py` is the first version. It has one child per outside component,
  which may violate 7(a), and chooses p_X among X-labelled edges.

**Instances.**
- Delaunay graphs on 160 random points, with 30% of the edges dropped while keeping the graph
  connected. Each direction of each edge gets a random weight from 1 to 19.
- Separators are fundamental cycles of a BFS tree of G[X], and leaves have size 14.
- **Virtual mode.** Separators may close through edges of the full Delaunay graph that are
  not in G, i.e. virtual edges.
- **Pendant mode.** This is the referee's family: 40 points, then k pendant leaves in every
  corner, with k = 3 or 6.

**Checks.**
- **Per level:**
  - every edge label stays in its bag;
  - corners between tiles of different bags are already in Γ_d;
  - Γ_{d+1} is connected;
  - faces of Γ_{d+1} = tiles;
  - one label per tile;
  - every port occurs once per tile and has edges;
  - every hub with an X-labelled edge is on Γ_{d+1} (Claim 4);
  - outside edges join ∂S*_X (Claim 5);
  - every edge of p_X is labelled X (Claim 3).
- **Claim 7.** tiles2 checks at most 4 + 2c_s label changes per separator vertex, |L_X| ≤
  8|S_X| per bag, and at most two outside children per separator vertex (7(a)). tiles.py
  checks at most 2k changes at a vertex with k outside components.
- **Monge:** (M) in all four orientations on every component of every tile, with exact
  distances in the boundary order.
- **Planarity:** planarity of the gluing inside every parent tile, and of H_X with its
  outside edges. Both are checked in a wheel model: one hub per disk, joined to its ports in
  order.
- **Rank lemma:** checked on every face with at least three corners.

**Results.** No check failed in any run.

| Run | Seeds | Monge checks | Tiles | Gluings | H_X | Hubs | Label-change checks | Rank checks |
|---|---|---|---|---|---|---|---|---|
| tiles2, plain | 4 | 551,516 | 1,450 | 527 | 92 | 1,588 | 1,141 | 688 |
| tiles2, virtual (59 virtual closings) | 6 | 802,464 | 2,452 | 831 | 156 | 2,686 | 1,943 | 1,015 |
| tiles2, pendant k = 3 | 3 | 10,896 | 1,310 | 315 | 78 | 715 | 472 | 103 |
| tiles2, pendant k = 6 | 3 | 10,208 | 1,208 | 319 | 80 | 724 | 472 | 103 |
| tiles, plain | 4 | 409,644 | 1,600 | 472 | 78 | 1,385 | 856 | 688 |
| tiles, virtual (61 virtual closings) | 8 | 891,812 | 3,304 | 941 | 171 | 3,051 | 1,921 | 1,341 |

- **tiles2.** |L_X| ≤ 2|S_X| in every bag, ports per child at most 3.3·|S_parent|, and 7(a)
  held throughout. The pendant family stays within these bounds once children are grouped
  as in [8].
- **P_X.** It never fired in tiles2, so Claim 3, step 3, rests on the proof. tiles.py used it
  5 times.
- **Referee's walk check** (`sim/ref2/walk_check.py`). This implements §3.5 from the
  text. It reconstructed every tile's port order from port records alone: 2,104 bag-level
  reconstructions on 16 seeds, with 20,944 port injections and 310 groupings of child tiles
  into parent tiles. There were 0 failures.

**Negative controls.** These confirm that the checks can fail.
- **tiles.** Shuffling the port order of a tile component broke (M) in 175 of 187 cases.
  Shuffling one sub-tile order made the gluing non-planar in 51 of 377 cases.
- **tiles2.** The same controls gave 178 of 198 and 64 of 368.

**Adversarial pass** (`sim/attack2/`, run on the draft before the referee's fixes).
- **Instances.** 24,850 instances on 15 families (trees with chords, cacti, outerplanar
  graphs, nested cycles, grids, wheels, stars, K_{2,m}, fans, brooms and others), with up to
  about 260 vertices and recursion depth up to 40. Separators were chosen adversarially:
  virtual closings at every corner, reused holes, digons, pinches, q along ancestor
  separators, chords on both sides, and forced P_X.
- **Results.** No failure of Claims 1 to 7, (T3), (T4), (T5) or the rank lemma, over 4.67
  million tiles, 1.55·10⁹ exact (M) inequalities, 305,000 LP checks and 9.3 million rebuilds
  of σ_τ from port records. P_X was used 320 times in the virtual configurations alone.
- **End to end.** Every child metric was replaced by another metric that is Monge only in
  its own order. After gluing, the parent still satisfied (M) in σ_τ.
- **(S7) rebuilt** (`s7_rebuild.py`). The three configurations, 720 instances: α* = 1 in
  σ_τ on all 2,618 LPs.
- **Negative controls.** Shuffled port orders broke (M) in 6,353 of 8,084 cases.
- **Child shapes.** The harness used either one child per outside component or a single
  outside child (`region=1`).
  - The first contradicts 7(a) on stars (`g1_inconsistency.py`). With [8]'s grouping, the
    same exhaustive search over all root separators of its star, windmill and K_{2,m}
    families gives a largest child of at most n/2 + 1 (`g1_grouped.py`).
  - With a single outside child, Claim 7 holds in the form 4 + 2c_s. The chord fan of
    `region_fan.py` has c_v = k − 1 and 2k − 2 label changes at v.
- **Side observation.** The harness's own separators often break Property 6, with up to 21
  bags per edge at one depth. They are not [8]'s separators, so this says nothing about
  (G1).

## 4. Tools

**Gluing.** Let A_1, …, A_k be digraphs with nonnegative arc weights and terminal sets
T_i ⊆ V(A_i). Let ~ be an equivalence relation on the disjoint union ⊔T_i.
- Glue(A; ~) is the disjoint union of the A_i with every ~-class identified to one vertex.
- All arcs are kept, so parallel arcs may appear.
- A *terminal image* is the image of a terminal.

**Lemma R1 (gluing keeps terminal approximation).** Suppose B_1, …, B_k are digraphs with
T_i ⊆ V(B_i) and, for all i and a, b ∈ T_i,
dist_{A_i}(a,b) ≤ dist_{B_i}(a,b) ≤ λ·dist_{A_i}(a,b). Then for all terminal images x, y,
dist_{Glue(A;~)}(x,y) ≤ dist_{Glue(B;~)}(x,y) ≤ λ·dist_{Glue(A;~)}(x,y).

*Proof.* Every vertex of a glued graph is one of two kinds: a terminal image, all of whose
preimages are terminals, or the image of exactly one non-terminal vertex of one piece. Every
arc belongs to exactly one piece.

Take a walk Q from x to y in Glue(A;~) and cut it at each visit to a terminal image.
- Each segment has no terminal image in its interior. So consecutive arcs share a
  non-terminal vertex, and the whole segment lies in a single piece A_i.
- Its ends lift to terminals t, t′ of T_i, so its length is at least
  dist_{A_i}(t,t′) ≥ dist_{B_i}(t,t′)/λ.
- Replace each segment by a shortest t to t′ path in B_i. The result is an x to y walk in
  Glue(B;~) of length at most λ·len(Q).

The same cutting applied to a walk in Glue(B;~), with dist_{B_i} ≥ dist_{A_i}, gives the
lower bound. ∎

Adversarial check: 8533 terminal-image pairs, including zero weights, ∞ distances and
identifications inside one piece, with 0 failures (`r1_glue.py`).

**Lemma R3 (replacing pieces keeps planarity).** Let Σ be the sphere or a closed disk.
Suppose:
- **(D1)** each A_i is disk-drawn in a closed disk D_i with T_i in order σ_i;
- **(D2)** there are continuous maps π_i : D_i → Σ, injective on int D_i, such that the sets
  π_i(int D_i) are pairwise disjoint and disjoint from ⋃_j π_j(∂D_j);
- **(D3)** for terminals t ∈ T_i and t′ ∈ T_j, π_i(t) = π_j(t′) iff t ~ t′, and no terminal
  has the same image as a non-terminal point of any ∂D_j.

Then two things hold.
- The union of the π_i-images of the drawings is a plane drawing of Glue(A; ~) in Σ.
- Let each B_i be disk-drawn with T_i in order σ_i. Draw B_i in D_i with T_i at the same
  points and apply π_i. This gives a plane drawing of Glue(B; ~) in Σ, and it meets
  ⋃ π_i(∂D_i) only at terminal images.

*Proof.* A disk-drawn B_i can be redrawn in D_i with T_i at the prescribed points, by a
homeomorphism of the disk that moves boundary points while keeping their cyclic order. So it
suffices to look at the union of images. Suppose two points of it coincide.
- **Both from interiors.** Then they come from the same i, and π_i is injective there.
- **One on a boundary.** Let p ∈ ∂D_i. Then p is a terminal, because the drawing meets ∂D_i
  only there. If π_i(p) = π_j(p′), then p′ is not in int D_j by (D2), so p′ ∈ ∂D_j. By (D3),
  p′ is a terminal and p ~ p′.

So distinct vertices are drawn at distinct points, and edges meet only at common ends. ∎

**Lemma R5 (LP with the right witness).** Take a cyclic order σ on T, finite values δ(a,b)
for a ≠ b, and α ≥ 1. LP(δ, σ, α) has variables d(a,b) ≥ 0 and these constraints:
- d(a,a) = 0;
- the cyclic Monge constraints (M) for σ, all four orientations;
- the triangle constraints d(a,c) ≤ d(a,b) + d(b,c);
- δ(a,b) ≤ d(a,b) ≤ α·δ(a,b) for a ≠ b.

Two claims:
- **Realization.** Every feasible d can be realized as in (G3), after multiplying by a
  common denominator and dividing the weights of the result back.
- **Feasibility.** Suppose a plane digraph O′ is disk-drawn with T in order σ, with finite
  distances and dist_{O′} ≤ δ ≤ α·dist_{O′} on T. Then d = α·dist_{O′} is feasible.

*Proof.*
- **Monge** follows from (G4); scaling keeps it.
- **Triangle constraints and the zero diagonal** hold for any distance function.
- **The bounds:** δ ≤ α·dist_{O′} is given, and α·dist_{O′} ≤ α·δ because dist_{O′} ≤ δ.
- **Realization:** the constraints are invariant under scaling, so d·(common denominator) is
  an integer quasimetric satisfying (M), and (G3) applies to it. ∎

The point is that the witness is the graph the oracle was built on, O′_C, and not C. So
α = 1+ε′ suffices at every level, independent of the depth. The witness only has to exist;
the centre never holds it.

**Lemma R6 (rounding).** Let K be a digraph with terminal set T, finite terminal distances,
and d_K(a,b) ≥ 1 for all a ≠ b. Let m = max d_K on T, and let η > 0 with η·|V(K)| ≤ ε′.
Cap every weight at m, then round it up to a multiple of η. The result K̂ has the same
embedding, weights that are multiples of η in [0, m+η], and, for all a ≠ b in T,
d_K(a,b) ≤ d_K̂(a,b) ≤ (1+ε′)·d_K(a,b).

*Proof.*
- **Capping changes no terminal distance.** A walk through a capped arc already has length
  ≥ m ≥ d_K(a,b), and other walks keep their lengths.
- **Rounding up never shortens a walk.** It lengthens a shortest terminal path (at most
  |V(K)| − 1 arcs) by less than ε′ ≤ ε′·d_K(a,b). ∎

Adversarial check: 2406 pairs with 0 failures; the worst (ratio − 1)/ε was 0.33
(`r6_round.py`).

**Lemma R7 (components in one disk).** Let A be disk-drawn in D with terminals T in order σ.
- **(a)** Distinct components C, C′ of A have non-crossing terminal sets: there are no
  a, c ∈ T ∩ C and b, d ∈ T ∩ C′ in cyclic order a, b, c, d.
- **(b)** For every component C with T_C := T ∩ C ≠ ∅, let B_C be disk-drawn with T_C in
  order σ restricted to T_C. Then the disjoint union of the B_C can be drawn in D with every
  terminal at its point, meeting ∂D exactly in T.

*Proof.*
- **(a).** Add a vertex z outside D, joined to T by arcs outside D in the order σ; the
  drawing stays plane. Suppose a, b, c, d interleave. The cycle z, a, (a path in C), c, z
  separates the arcs zb and zd near z, so b and d lie on different sides of it. A b to d path
  in C′ avoids the cycle, which contradicts the Jordan curve theorem.
- **(b).** Take D to be the unit disk.
  - **Disjoint hulls.** By (a) the sets T_C do not interleave. So for any two of them a
    line separates them, and their convex hulls are disjoint.
  - **A disk per component.** For each C, choose a closed disk Δ_C ⊆ D near the hull of
    T_C with Δ_C ∩ ∂D = T_C:
    - the hull itself if |T_C| ≥ 3;
    - a thin lens around the chord if |T_C| = 2;
    - a small disk tangent to ∂D at the point if |T_C| = 1.
  - Draw B_C in Δ_C with T_C at its points. ∎

## 5. Lemma 15, repaired

**Lemma 15′.** Assume Lemma 14′, and let ε′ ∈ (0,1]. For every non-root bag X and every
component C of the piece of a tile τ of X, the centre c_X ends up holding a plane digraph
O′_C with three properties:
- **(I1)** O′_C is disk-drawn with the ports of C in the order σ_τ.
- **(I2)** For all ports a, b of C:
  dist_C(a,b) ≤ dist_{O′_C}(a,b) ≤ (1+ε′)^{3h(X)}·dist_C(a,b).
- **(I3)** The weights are multiples of some η_X with 1/η_X ∈ ℕ, and are at most poly(n),
  so N = poly(n)/η_X = poly(n) in (G5).

c_X also holds the (G5) oracle labels of each O′_C with parameter ε′ on its ports. By (T2)
this is Õ(D/ε′) words in total. If X is not a leaf, and also when X is the root, c_X further
holds a plane digraph H_X with:
- for all a, b ∈ ∂S⁺_X,
  dist_{G[X]}(a,b) ≤ dist_{H_X}(a,b) ≤ (1+ε′)^{3h(X)}·dist_{G[X]}(a,b);
- (I3);
- its oracle labels on ∂S⁺_X.

The whole tree is processed in Õ(D/ε′) rounds.

*Leaf L.* c_L gathers G[L] as in [1], together with the corners of Γ at its vertices, and
builds the pieces of its tiles and their orders (T5). It sets O′_C := C for every component
C. This is exact, which is (I2) at height 0.
- (I1): C meets ∂D_τ only at its own ports, so it is disk-drawn by (T3).
- (I3) holds with η = 1 by (W1).

*Non-leaf X, after all children.*
1. **Broadcast.** For every child Y, every tile τ′ of Y and every component C of its piece,
   c_Y sends c_X the order σ_{τ′} on C and the oracle labels of O′_C on its ports, together
   with the port records of (T5). By (T2) this is Õ(D/ε′) words per bag, even when X has
   Õ(D) children.
2. **LP.** For each such C, let δ_C(a,b) be the oracle answer for ports a, b of C. Then
   dist_{O′_C} ≤ δ_C ≤ (1+ε′)·dist_{O′_C}. Solve LP(δ_C, σ_{τ′}, 1+ε′).
   - It is feasible by Lemma R5, with witness O′_C. The witness is disk-drawn with the
     ports of C by (I1) for Y. Its distances are finite by (I2) for Y, since C is connected
     and so strongly connected by (W2).
   - Its solution d_C satisfies dist_{O′_C} ≤ d_C ≤ (1+ε′)²·dist_{O′_C}.
3. **Realize.** Realize d_C by K_C via (G3), disk-drawn with the ports of C in order
   σ_{τ′}. Drop the components of K_C that carry no port.
4. **Round.** Let η_X := 1/⌈max_C |V(K_C)|/ε′⌉, and round every K_C to K̂_C by Lemma R6.
   - The hypothesis d_{K_C} ≥ 1 holds. Distinct ports of C are distinct vertices of C, even
     when they are copies of one vertex of G. So d_C ≥ dist_C ≥ 1 by (I2) and (W1).
   - Combining steps 2 to 4 with (I2) for Y: on the ports of C,
     dist_C ≤ dist_{K̂_C} ≤ (1+ε′)³·(1+ε′)^{3h(Y)}·dist_C ≤ (1+ε′)^{3h(X)}·dist_C.
5. **Glue.** For a child tile τ′, let K̂_{τ′} be the disjoint union of the K̂_C over the
   components C of its piece. Set:
   - Q′_τ := Glue(K̂_{τ′} over the child tiles τ′ inside τ; ~_τ), for every tile τ of X
     (X not the root);
   - H_X := Glue(K̂_{τ′} over all child tiles, and the outside edges of X with their
     weights in G; ~_G).

   Then:
   - **Distances.** By (T4a) and (T4b), the same gluings of the child tile pieces give P_τ
     and G[X]. Outside edges are exact pieces. Lemma R1 gives the factor (1+ε′)^{3h(X)}
     against P_τ on its ports, and against G[X] on ∂S⁺_X.
   - **Planarity.** By R7(b), K̂_{τ′} is disk-drawn in D_{τ′} with the ports of τ′ in order
     σ_{τ′}. Lemma R3 with (T4c) then gives:
     - Q′_τ is drawn in D_τ and meets ∂D_τ exactly at the ports of τ, in order σ_τ;
     - in S², with X's child tiles replaced and all other tiles of Γ_{d+1} kept, H_X is a
       subgraph of the resulting plane drawing. The outside edges are edges of other tiles.
   - **O′ and (I1).** Let C* be a component of P_τ. Let O′_{C*} be the union of the K̂_C over
     the child components C that the gluing maps into C*. Two components of P_τ share no
     vertex, so no ~_τ-class mixes them, and Q′_τ is the disjoint union of the O′_{C*}.
     O′_{C*} is disk-drawn in D_τ with exactly the ports of C*, in the order σ_τ, and R1
     gives (I2) on these ports.
   - **(I3).** The weights of the K̂_C are multiples of η_X. The outside edges have integer
     weights, which are multiples of η_X since 1/η_X ∈ ℕ. All weights are at most
     (1+ε′)²·max dist_{O′_C} + η_X or W, which is poly(n).
6. **Oracles.** Build the (G5) oracles of every O′_{C*} and of H_X locally, with parameter ε′.
   Plane embeddings for them come from any planarity algorithm; Lemma R3 shows that they
   exist.

The rounds are those of [1]: one broadcast of Õ(D/ε′) words per level, levels in sequence,
and Õ(D) rounds per level for Γ (T5). Steps 2 to 6 are local. ∎

Bookkeeping: the leaf oracle's error is paid at the parent, in step 2. A query to the oracle
of H_X costs one more factor 1+ε′, so labels built from H_X are within (1+ε′)^{3h(X)+1}
(§6), and those built at the root within (1+ε′)^{3H+1}.

Compared with [1]:
- Steps 2 to 4 replace [1, Thm 2], which fixes (S1) to (S3).
- Step 5 replaces steps 3 and 4 of [1] with a defined construction whose planarity is
  Lemma R3 with (T4c). This fixes (S4).
- Working one component at a time, with (W2), fixes (S5).
- §3 replaces Def. 6 and Lemma 14, which fixes (S7).

## 6. Lemma 16, repaired (the labels Theorem A uses)

**Lemma 16′.** Assume Lemma 15′. For every bag X, v ∈ X and h ∈ ∂S⁺_X, the vertex v ends up
knowing d̃_X(v,h) and d̃_X(h,v) with
dist_{G[X]} ≤ d̃_X ≤ (1+ε′)^{3h(X)+1}·dist_{G[X]}.
For a leaf L, v knows dist_{G[L]}(u,w) exactly for all u, w ∈ L; Lemma V uses this for its
leaf term. The rounds are Õ(D/ε′) per level, so Õ(D/ε′) in total.

*Construction.*
- **Leaves.** All of G[L] is broadcast inside L, as in [1].
- **Broadcast for non-leaf X.** The oracle labels of H_X on ∂S⁺_X go to every vertex of X, as
  in [1]: Õ(D/ε′) words per bag, all bags of one level in parallel by Property 6. Let δ^H be
  the answers. By Lemma 15′ and (G5), dist_{G[X]} ≤ δ^H ≤ (1+ε′)^{3h(X)+1}·dist_{G[X]} on
  ∂S⁺_X.
- **Hubs.** For v ∈ ∂S⁺_X, set d̃_X(v,h) := δ^H(v,h).
- **Non-hubs.** For v ∉ ∂S⁺_X, v lies in exactly one child X_i by (7a). Set

  d̃_X(v,h) := min( d̃_{X_i}(v,h) if h ∈ X_i ; min over t ∈ S_X ∩ X_i of
  d̃_{X_i}(v,t) + δ^H(t,h) ),

  and symmetrically for d̃_X(h,v). The child labels exist because
  h ∈ ∂S⁺_X ∩ X_i = ∂S*_{X_i} and S_X ∩ X_i ⊆ ∂S*_{X_i} are hubs of X_i.

*Proof.* **Lower bound.** Every candidate is at least the length of a walk in G[X], since
G[X_i] ⊆ G[X].

**Upper bound.** Let P be a shortest path from v to h in G[X], and let x, y be consecutive
vertices of P outside S_X. By (7a) each lies in exactly one child. By (7b) the edge xy cannot
join two different children, since a path between different children meets S_X. So,
starting from v, every vertex of P before the first vertex of S_X lies in X_i. There are two
cases.
- **P avoids S_X.** Then P ⊆ G[X_i], so h ∈ X_i, and the first candidate is at most
  (1+ε′)^{3h(X_i)+1}·|P|.
- **P meets S_X.** Let t be its first vertex in S_X and x the vertex before it, with
  x ∈ X_i. By (7c′), t ∈ X_i. So the prefix of P up to t lies in G[X_i], and the second
  candidate is at most (1+ε′)^{3h(X_i)+1}·|P[v,t]| + (1+ε′)^{3h(X)+1}·|P[t,h]|.

In both cases d̃_X(v,h) ≤ (1+ε′)^{3h(X)+1}·dist_{G[X]}(v,h). The direction h to v is
symmetric, with the last vertex of S_X in place of the first. ∎

Adversarial check: 90,940 (v,h) checks per child model, in both directions, with 0 failures
(`l16.py`). (7c′) held in every run, even in the model where full (7c) fails.

## 7. Parameters

Take ε′ = ε / (2(3H+1)). Then (1+ε′)^{3H+1} ≤ e^{ε/2} ≤ 1+ε for ε ∈ (0,1].
- **Sizes and rounds.** Since ε′ = Θ(ε/log n), as in [1] up to the constant, labels are
  Õ(D/ε′) = Õ(D/ε) and rounds are Õ(D/ε).
- **(I3).** It keeps log N = O(log n) in (G5), given 1/ε ≤ poly(n); Theorem A uses
  ε₀ = Θ(1/log n).

## 8. What this settles, and what it does not

- **Proved, and confirmed by both passes.** The analytic layer:
  - Lemmas R1, R5 and R6, and the error recursion (1+ε′)^{3h+1};
  - the d ≥ 1 and finiteness chain;
  - the parameters.

  This fixes (S1), (S2), (S3), (S5) and (S6).
- **Proved here, refereed, and attacked in its earlier draft.** Lemma 14′ (§3), with
  Lemmas R3 (restated) and R7. The referee's fixes are in. The adversarial pass on the
  earlier draft found nothing that these fixes do not cover. This fixes (S4) and (S7). The
  checks of §3.7 found no counterexample.
- **Black boxes.**
  - (G1) in the form (G1′), read off [8]'s construction, with T_X in place of [1]'s
    Property 4.
  - (G3), which is [10, Thm 1] (refereed). The centres search for K exhaustively, which
    CONGEST allows.
  - (G4), (G5) and (G6).
- **Consequence.** Once an adversarial pass on the fixed §3 is in, Theorem A, and through
  it Theorems B, C and C′, rest only on the black boxes. Until then they are
  conditional on Lemma 14′. [1, Thm 4] is in the same position: its proof goes through
  [1, Lemma 14], and §3 with §5 repairs it.

**Ratings.**
- **The repair: minor.** It changes no bound. The tile construction is simpler than [1]'s hub
  network: nothing is cut, and the pieces are disks by construction. But it repairs someone
  else's lemma, and its value is that Theorem A and [1, Thm 4] become correct.
- **The finding that [1, Lemma 14] fails: modest.** It is a correctness gap in the main
  CONGEST result of an unrefereed paper.
