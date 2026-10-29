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

Status (2026-10-29):
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
- **Second adversarial pass**, on this text (§3.7). Nothing in §3, in Claim 7, in P_X, or in
  the parts of Lemmas 15′ and 16′ that use them failed on 14,500 instances. It found one
  serious problem in the assumptions, (S9): Property 6 is false for induced bags. That
  breaks the round count, not correctness. It also corrected four details of our reading of
  [8], and showed that one step of [8] can add more than one component to T[X] (§1).
- **§9 (new)** repairs (S9). Bags carry the sides of the edges they were cut from, and every
  edge lies in at most two of these region graphs per depth. §9 also proves the component
  bound for T_X that [8] states, with one more log factor. §9 has had a referee pass, whose
  fixes are in, and an adversarial pass, which broke nothing.
- **Status.** Lemma 14′ and the labels are correct given the black boxes of §1. No human has
  checked them. The Õ(D/ε) round bound for the labels, and with it the Õ(D) of Theorem A,
  holds in the region form of §9, with no black box beyond those of §1: the separator is
  Lemma B5 (§9.6), which is deterministic. So Theorem A is deterministic, given a
  deterministic planar embedding and deterministic face identifiers.

## 1. What we take from [1]

Notation is that of [1, Sec. 5]:
- **The decomposition tree.** Its height is H = O(log n). h(X) is the height of bag X (leaves
  have height 0), and d(X) its depth (the root has depth 0).
- **Per bag X:**
  - T_X: a spanning tree of G[X] with diameter O(D log n). [8, Sec. 4.2, Step 1] builds it
    from T[X] plus O(log n) edges. [1, Lemma 9] states the stronger Property 4, that T[X]
    itself is a spanning tree of height O(D), but [8, Def. 4.1 (6)] only gives O(log n)
    components for T[X]. We use T_X, which costs one log factor in sizes and rounds.
    The O(log n) components come from [8, Claim 4.6, Lemma 4.7], which add one component
    per level. That step is false: a child met S_X in two arcs and went from 1 to 3
    components in one step (second adversarial pass, `sim/attack3/lp46_demo.py`). In all
    faithful runs the total stayed at most depth + 1, and with adversarial z_s at most
    depth + 3. In the region form of §9 the bound is proved: c(X) = O(log² n) (Lemma B1(e)),
    so T_X has diameter O(D log² n), and sizes gain one more log factor (§9.5).
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
      side of z_s go to different copies. An unsplit vertex keeps all its edges into the
      outside wedge; edges drawn inside S_X are not in the auxiliary graph.
    - The one child that is disconnected without the virtual edge is split into its two
      components.
    - A vertex outside S_X has all its edges in the auxiliary graph, which gives the second
      item. The splitting rule gives contiguity.
    - So s lies in X_in and in at most two outside children, which is 7(a).
    - Details. [8] also makes a child of every auxiliary component that consists of separator
      vertices only; (G1′) leaves these out, since they contain no vertex outside S_X. When
      S_X runs through a hole of X, "out of the region" is not defined at some s, and s is
      not split. At a vertex that S_X visits twice, one z_s is kept. 7(a) held in every run.

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
  - **Polynomial local time.** The proof in [10] is a greedy construction that inserts one
    terminal shortest path at a time, but [10] states a running time only for finding the
    order ([10, Thm 2], O(|T|⁶)), not for the construction. A polynomial bound needs either
    that analysis or [1, Thm 2] with its order guarantee checked. Nothing below needs it.
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
- **(S9) Property 6 is false for induced bags.** [1, Lemma 9 (6)] says that at every depth
  each edge lies in at most two subgraphs G[X], and [8, Lemma 4.3 (8′)] says the same. Both
  fail on G_m, which is K_{2,m} plus the edge uw: planar, with D = 2 (second adversarial
  pass, `sim/attack3/p6.py`).
  - Let B be the set of bags that contain u and w. Take a non-leaf X ∈ B and a petal
    a ∈ X ∖ S_X. Then a lies in exactly one child X_i, and by (7c′), or by [8, Def. 4.1 (3)],
    the edges ua and wa lie in G[X_i]. So X_i ∈ B.
  - Hence every petal ends in a separator or a leaf of a bag of B, and m ≤ |B|·O(D log n).
    With at most two bags of B per depth, |B| = O(log n), so m = O(log² n), which is false
    for large m.
  - Measured with n = 102, 202 and 402: up to 32, 64 and 128 bags of one depth contain uw.
  - The argument uses only the height, the bounds on |S_X| and on leaves, (7a) and (7c′).
    So no decomposition with these properties satisfies Property 6 on G_m. The overview of
    [8] describes the intended property for the edges a bag owns ("one from each side of
    that edge"), which is not the same as induced subgraphs.
  - **What it breaks.** Correctness does not use Property 6: no proof of Lemmas 14′ to 16′ or
    of Lemma V does. The round counts do. [1] and these notes run all bags of one depth in
    parallel because of Property 6: the Γ computations (§3.5), the transfers of §5 step 1
    and §6, and the convergecast of Lemma V (NOTES). On G_m with T rooted at u, Ω(n/log² n)
    bags of one depth each send Õ(D) words across uw. So the Õ(D/ε) bound of [1, Thm 4], and
    the Õ(D) of Theorem A, are not proved as written.
  - **Repair: §9.** Bags carry sets of edge sides, and region graphs R_X replace G[X]. Each
    edge then lies in at most two region graphs per depth (Lemma B1(a)), and §3 to §6 and
    Lemma V carry over (§9.5).
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

**Building Γ_{d+1}.** All of this runs for all bags of depth d in parallel. [1] bounds the
congestion of such steps by 2 through Property 6, which is false for induced bags (S9). In
the region form, Lemma B1(a) gives congestion 2 (§9.6).
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

- **tiles2.** |L_X| ≤ 2|S_X| in every bag, ports per child at most 3.33·|S_parent|, and 7(a)
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
- **Property 6.** The harness's separators often break Property 6, with up to 21 bags per
  edge at one depth. The second pass showed that on some graphs every decomposition with
  the other properties breaks it (S9).

**Second adversarial pass** (`sim/attack3/`, on this text).
- **Instances.** 14,500 instances in nine sweeps, n ≤ 510, depth ≤ 16, 1.12 million bags.
  The families are Delaunay graphs with dropped edges, jittered grids, K_{2,m} with a chord
  and subdivided petals, fans, nested rings, Delaunay graphs with pendant leaves in every
  corner, and flowers. 5,000 instances follow (G1′) faithfully (T_X ⊇ T[X] from a BFS tree,
  inherited z_s). The others use other trees T_X to force P_X.
- **Results.** No failure.
  - Claim 7: at most 3 + 2c_s label changes at a vertex in 2.5 million checks;
    |L_A|/|S_A| ≤ 4.75; |J_X| ≤ 0.98·Σ_{A ∈ Anc*(X)} |N_A|.
  - P_X was forced 5,327 times, with up to 54 edges.
  - Lemma 15′: 2.4 million end-to-end gluings with replaced child metrics; R1 on 24.6
    million pairs; (M) in σ_τ on 4.3·10⁹ inequalities; H_X planar in all 324,191 cases;
    rounding and (I3) in exact arithmetic (`r6check.py`).
  - Lemma 16′: 3.6·10⁸ checks with adversarial hub oracles.
  - (7a), (7b), (7c) and (7c′) held at all 324,191 separators.
- **Negative controls.** Shuffled port orders, shuffled wheel rims, a dropped corner of L_X,
  a removed P_X and a dropped hub term in Lemma 16′ were all detected.
- **Findings.** (S9), the step of [8] in §1, and the details of (G1′) in §1.

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

*Lean.* `glue` in `lean/SsspFlow/Tools.lean` proves the combinatorial core in walk form. A walk
between terminal images cuts into segments of one piece with no terminal image inside
(`decomp`), and matches of the segments compose. The quotient Glue(A; ~) itself is not
formalized: its two properties used above (every arc in one piece, all arcs at a non-terminal
vertex in one piece) enter as hypotheses, and so does dist_{B_i} ≤ λ·dist_{A_i} on segments.

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

*Lean.* `rounding` in `Tools.lean`, in walk form, with `rnd_bounds` for the range of the new
weights.

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
and Õ(D) rounds per level for Γ (T5). Steps 2 to 6 are local. ∎ (The round count needs the
bags of one level to run in parallel. [1] uses Property 6, which fails (S9); the region form
of §9 gives it, §9.6.)

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
  in [1]: Õ(D/ε′) words per bag, all bags of one level in parallel. Property 6 is false for
  induced bags (S9); the region form of §9.6 gives the parallel schedule. Let δ^H be
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

*Lean.* `labelOut` and `labelIn` in `lean/SsspFlow/Labels.lean` prove one level, in both
directions. (7c′) with (7b) enters as a closure hypothesis: an arc of G[X] at a vertex of
X_i ∖ S_X stays in X_i. The child factor may be any λ_i ≤ λ.

## 7. Parameters

Take ε′ = ε / (2(3H+1)). Then (1+ε′)^{3H+1} ≤ e^{ε/2} ≤ 1+ε for ε ∈ (0,1].
- **Sizes and rounds.** Since ε′ = Θ(ε/log n), as in [1] up to the constant, labels are
  Õ(D/ε′) = Õ(D/ε) and rounds are Õ(D/ε).
- **(I3).** It keeps log N = O(log n) in (G5), given 1/ε ≤ poly(n); Theorem A uses
  ε₀ = Θ(1/log n).
- **Lean.** `params` in `Tools.lean` proves the inequality, and `level_step` the chain of
  factors in step 4 of Lemma 15′.

## 8. What this settles, and what it does not

- **Proved, and confirmed by both passes.** The analytic layer:
  - Lemmas R1, R5 and R6, and the error recursion (1+ε′)^{3h+1};
  - the d ≥ 1 and finiteness chain;
  - the parameters.

  This fixes (S1), (S2), (S3), (S5) and (S6). The combinatorial core of R1, Lemma R6, one
  level of Lemma 16′ and the parameters are also checked in Lean (`Tools.lean`,
  `Labels.lean`).
- **Proved here, refereed, and attacked twice.** Lemma 14′ (§3), with Lemmas R3 (restated)
  and R7. The referee's fixes are in, and the second adversarial pass, on this text, found
  nothing in §3. This fixes (S4) and (S7).
- **The round count** (S9). Property 6 is false for induced bags, so the parallel schedule
  of [1] needed a new argument. §9 gives one with region bags: Lemma B1, proved, refereed
  and attacked once, with the separator of Lemma B5, which is deterministic.
- **Black boxes.**
  - (G1) in the form (G1′), read off [8]'s construction, with T_X in place of [1]'s
    Property 4.
  - (G3), which is [10, Thm 1] (refereed). The centres search for K exhaustively, which
    CONGEST allows.
  - (G4), (G5) and (G6).
- **Consequence.** Given the black boxes, Theorem A, and through it Theorems B, C and C′,
  are correct algorithms with the stated round bounds, in the region form of §9. No human
  has checked the proofs. [1, Thm 4] is in the same position: its proof goes through
  [1, Lemma 14], which §3 with §5 repairs, and through Property 6, which §9 replaces.

**Ratings.**
- **The repair: minor.** It changes no bound. The tile construction is simpler than [1]'s hub
  network: nothing is cut, and the pieces are disks by construction. But it repairs someone
  else's lemma, and its value is that Theorem A and [1, Thm 4] become correct.
- **The finding that [1, Lemma 14] fails: modest.** It is a correctness gap in the main
  CONGEST result of an unrefereed paper.
- **(S9): modest.** It removes the round bound of the main theorem of [1] as written, and it
  shows that [8, Def. 4.1] together with [8, Lemma 4.3 (8′)] has no model on a simple
  family. Whether results of [8] are affected depends on how its algorithms use the bags;
  its overview describes the version for owned edges, which is not refuted.
- **The region repair (§9): modest.** See §9.8.

## 9. Region bags: the round count (repair of (S9))

(S9) comes from the induced subgraphs. On G_m the edge uw lies in G[X] for Ω(n/log² n) bags of
one depth, although none of them was cut along it. The repair gives every bag the part of the
plane it was cut from, and the edges drawn there, instead of G[X]. This is what [8]'s proof of
Lemma 4.3 (8′) uses. That proof is topological: an edge that lies in the closure of O(X) for
more than two disjoint regions O(X) of one depth would have to run along the boundary of
three of them.
- **Tame regions only.** That last step needs regions that are unions of faces or triangles,
  as [8]'s are; comb-shaped open sets let one arc lie on the boundary of many.
- **(8a) fails for induced bags.** [8, Def. 4.1 (8a)] asserts the containment for the induced
  G[X]. For tame regions it then implies (8′), which G_m refutes for every decomposition with
  the other properties. [8]'s own X⁺ already breaks (8a) when S has an outside chord.
- **Region graphs.** With region graphs in place of G[X], (8′) becomes Lemma B1(a). The
  interior of Ω_X (below) can be disconnected, at pinches, so region bags satisfy (8′) but not
  Def. 4.1 (8) literally. Nothing below uses (8) itself.

### 9.1 Sides, regions, holes

- **Sides.** Every edge e of G has two sides, one on each side of e (a bridge has the same face
  on both). In the radial
  graph R of §3.1, the side (e, σ) is the triangle t(e, σ) spanned by the two ends of e and the
  face node on side σ. These triangles tile S². Two triangles are *adjacent* if they share a
  side, which is either an edge of G or an R-edge (a *spoke*).
- **Region bags.** Every bag X carries a set E_X of sides.
  - Its *region graph* R_X consists of the edges with at least one side in E_X and their ends;
    from now on V(X) := V(R_X).
  - Its *region* is Ω_X, the union of the triangles of E_X. So R_X is the set of edges whose
    curves lie in Ω_X.
  - The root has every side, so R_root = G and Ω_root = S².
- **Holes.** A hole of X is a component of S² ∖ Ω_X, and ν(X) is the number of holes.
- **Trees.** T is a BFS tree of G of height at most D. T_X is T ∩ R_X plus connectors (edges of
  R_X that join two components) until it spans R_X. This is [8, Sec. 4.2, Step 1] with T[X]
  replaced by T ∩ R_X. c(X) is the number of components of T ∩ R_X.

### 9.2 The construction

Let X be a non-leaf. S_X is the separator of Lemma B5 (§9.6) for R_X and T_X: a path q_X of
T_X plus a closing edge yz. The closing edge is real (an edge of R_X) or virtual (drawn in a face
of R_X). S_X is a simple closed curve with an inside D_in and an outside D_out. The sides of
E_X go to the children as follows, and each side goes to exactly one child.
- **Inside parts.** The inside sides are:
  - all sides of edges with an end inside S_X;
  - both sides of edges between separator vertices drawn inside (inside chords);
  - the inside side of each edge of S_X.

  The inside parts are the components of the graph of these edges. Each is a child and keeps
  the sides it contains.
- **Outside children.** [8]'s auxiliary graph, built from the remaining sides only. These are
  the edges with an end outside, the outside chords, and the outside sides of the edges of
  S_X.
  - As in [8], a separator vertex s is split into two copies at a direction z_s, and the sides
    on either side of z_s go to different copies. If s has no recorded direction, or if it lies
    in the inside wedge of S_X, s is not split (`engine_r.py` counts the latter as
    `z_inherited_in_inside_wedge`).
  - A virtual closing edge joins its two ends.
  - The outside children are the components of this graph, split further into components of
    real edges.
- **Directions z_s.** When s lies on S_A, every child Y of A records at s a direction into the
  wedge of S_A on the other side, which lies outside Ω_Y, and descendants inherit it. So z_s
  always points into a sector of s outside the region. This is [8]'s "out of the region".
- **Labels.** Rules 1 and 2 of §3.2 stay. Rule 3 becomes:
  - 3_R. If both ends of e lie on S_X, then λ_{d+1}(e) is the inside part that holds a side of
    e if there is one, and otherwise the outside child that holds a side of e.

Two choices are [8]'s and are needed below: T_X ⊇ T ∩ R_X, and a separator vertex, if split
at all, is split at a direction outside Ω_X. No bound needs the split itself: without it,
(F1) below is trivial and s lies in at most one outside child. Runs with T_X unrelated to T
(DFS or random spanning trees) reached c(Y) = 41 at small depth, and runs with random z_s
reached a_Y = 7 with no hole (§9.7).

Three things differ from [8]:
- there can be several inside parts, where [8] has one X_in ⊇ S_X;
- only sides of E_X are handed down, so an edge of S_X whose inside side lies in a hole of X
  lies in no inside part;
- outside children that consist only of chords, or only of edges of S_X, are kept.

### 9.3 Properties

**Lemma B1 (region bags).** Let X be a non-leaf at depth d. Then:
- **(a) Property 6_R.** Every side of E_X lies in exactly one child. Hence for each depth, the
  sets E_X of the bags of that depth are disjoint, and every edge lies in at most two region
  graphs R_X of that depth.
- **(b) (7a_R) and (7c′_R).** A vertex x ∉ S_X lies in exactly one child, and that child holds
  every side of every edge of R_X at x. A vertex s ∈ S_X lies in at most one inside part and in
  at most two outside children.
- **(c) (7b_R).** Every R_Y is connected. A path in R_X that avoids S_X lies in one child's
  region graph.
- **(d) Claim 1_R.** λ_d(e) = X implies e ∈ R_X, and λ_{d+1}(e) is λ_d(e) or a child of it.
- **(e) Components.** c(Y) ≤ c(X) + max(1, ν(X)) + 1 and ν(Y) ≤ ν(X) + 1 for every child Y.
  So ν ≤ d at depth d, c(X) ≤ 3 + (d − 1)(d + 2)/2 for d ≥ 1, and with d = O(log n):
  c(X) = O(log² n) and diam(T_X) ≤ c(X)·(2D + 1) = O(D log² n).

*Proof of (a) to (d).*
- **(a)** holds by construction. Induction over the depth gives the disjointness, and an edge
  has two sides.
- **(b).** Take x inside S_X. Every edge at x has an end inside, so all of its sides in E_X
  are inside sides. These edges share x, so they lie in one inside part. Take x outside. All of its
  edges meet at the single auxiliary node x, so they lie in one auxiliary component, and they
  share x, so they lie in one real component. For s ∈ S_X, all inside sides at s belong to
  edges at s, which share s, so they lie in one inside part. On the outside there are two
  copies of s.
- **(c).** The first part holds by construction. For the second, let x, x′ be consecutive
  vertices off S_X on the path; by (b), the edge xx′ lies in the child of x and in the child
  of x′.
- **(d).** Let e = uw ∈ R_X. If u ∉ S_X, then rule 1 picks u's child, which holds all sides of
  e by (b), and the same holds for w. If u, w ∈ S_X, a side of e lies in E_X and goes to some
  child, and rule 3_R picks a child that holds one. ∎

(e) is proved in §9.4. The value of (a) is that it is a statement about sides, which stay
disjoint, and not about vertex sets. A vertex may lie in many bags of one depth (on G_m, u
does), but CONGEST charges edges, and every edge carries the traffic of at most two bags per
depth.

### 9.4 Proof of Lemma B1(e)

Let Y be a child of X on side s ∈ {in, out}, and let D := D_s.
- **The arc graph** A_Y has the vertices of S_X that lie in V(Y), and the real edges of S_X
  whose side s lies in E_Y. a_Y is its number of components.
- The proof has three steps: c(Y) ≤ c(X) + a_Y (Lemma B2), a_Y ≤ max(1, ν(X)) + 1
  (Lemma B3), and ν(Y) ≤ ν(X) + 1 (Lemma B4).

**Lemma B2.** c(Y) ≤ c(X) + a_Y.

*Proof.* Let K be a component of T ∩ R_X.
- **One segment per component.** T_X contains K. Contracting the components of T ∩ R_X turns
  T_X into a tree, so the path q_X meets K in one subpath σ_K, which may be empty or a single
  vertex.
- **K is σ_K plus hanging subtrees.** σ_K is a path in the tree K. So K consists of σ_K and
  subtrees H, each attached by one edge e_H at a vertex of σ_K. An edge of K with both ends on
  σ_K is an edge of σ_K, since K has no cycle.
- **A hanging subtree goes to one child.** H avoids S_X, so it lies inside or outside. By
  Lemma B1(b), H and e_H go to a single child, and that child contains the attachment vertex.
- **Edges of σ_K.** These are edges of S_X, and their side s goes to a child on side s.

So every component of K ∩ R_Y contains a vertex of σ_K. Two vertices of σ_K in one component of
σ_K ∩ A_Y are joined by T-edges of R_Y. Hence K contributes at most the number of components
of σ_K ∩ A_Y to c(Y). A component K with σ_K = ∅ lies in one child and contributes at most 1.

Now count. The σ_K are disjoint subpaths of q_X. Cutting the cycle S_X at the closing edge
leaves at most a_Y + 1 disjoint subpaths of q_X; only an arc through a real closing edge is
cut. For two families of disjoint subpaths of a path, the intersection graph is a forest. So
the number of intersecting pairs is at most the number of subpaths involved minus one, which
gives Σ_K #comp(σ_K ∩ A_Y) ≤ k_Y + a_Y. Here k_Y is the number of components K with
σ_K ∩ A_Y ≠ ∅. These K, together with the K that have σ_K = ∅ and lie in Y, are distinct
components of T ∩ R_X. Hence c(Y) ≤ c(X) + a_Y. ∎

**Lemma B3.** a_Y ≤ max(1, ν(X)) + 1. The +1 occurs only when the closing edge is virtual.

*Setting.*
- **The closing curve.** A virtual closing edge comes from Lemma B5 with a face Φ of R_X and a
  corner of Φ at y and at z, where the curve leaves y and enters z. We choose its drawing.
  - **Fans.** R_X is connected, so Φ is an open disk; lift it to a closed disk D_Φ along its
    boundary walk. The corners at y and z become two boundary points.
    - The triangles of E_X in Φ fall into *fans*: maximal runs of consecutive triangles of one
      face f of G, around its face node.
    - A fan is a closed disk. It meets ∂D_Φ in one boundary segment, its edges, and its apex
      f lies inside. Fans with different apexes meet at most in boundary points.
    - Every other point of int(D_Φ) lies in a hole of X, and the holes of X inside Φ are the
      components of int(D_Φ) minus the fans.
  - **Connectivity.** Let U be the union of the open fans. Then int(D_Φ) ∖ U is
    path-connected: a path that enters an open fan can go around it along its inner boundary
    (its two outer spokes and its apex), which lies in no other open fan. Two holes meet only at
    apexes.
  - **The drawing.**
    - Leave y through the hole sector of its corner. If the corner is covered by two triangles
      of one fan, leave instead along their shared spoke to the apex, and treat z the same way.
    - Then follow a shortest path in the incidence graph of holes and apexes, which is
      connected by the previous point. Join consecutive apexes by simple arcs inside the hole
      between them.
  - **Result.** The curve crosses no open triangle of E_X: it runs along spokes at y and z and
    through apexes. It meets every hole of X in at most one arc.
  - **Independence of the drawing.** With the corners fixed, a triangle of E_X in Φ goes in or
    out according to the arc of ∂D_Φ that its edge lies on. So the drawing changes no side of
    E_X, and the engine's straight segment inside a face of G gives the same sides.
  - **Consequence.** Every triangle of E_X lies in the closure of D_in or of D_out.
- **Regions of side s.** These are the children on side s and the components of
  (S² ∖ Ω_X) ∩ D.
  - A hole of X is a complement component of the connected set Ω_X (connected since R_X is),
    hence simply connected. It meets S_X in at most one arc of the closing curve, and a crosscut
    splits a simply connected domain into two, so it has at most one component on side s.
  - So there are at most ν(X) hole regions.
- **(F1) Adjacent triangles of E_X on side s lie in the same child.**
  - Shared edge: an edge e ∉ S_X has all its sides in one child.
  - Shared spoke at v: the two triangles cover the corner of v between their edges, so that
    corner lies in Ω_X.
    - If v ∉ S_X, use Lemma B1(b).
    - If v ∈ S_X and s = in, both triangles lie in the inside part at v.
    - If s = out, z_v points out of Ω_X, so it does not separate the two triangles. Both go
      to the same copy of v, hence to the same auxiliary and real-edge component.
  - Likewise, two adjacent triangles on side s that are not in E_X lie in one hole region.

*Pieces.* Let D′ be closure(D) minus small open disks around the vertices of S_X and around the
face nodes on the closing curve; it is a closed disk. Remove also small open disks around the
other face nodes of R. A *piece* is a component of what remains of a child Y on side s.
- A child is connected through real edges and vertices, never through a face node alone. So
  its pieces are glued only at vertices of S_X.
- Pieces of different children are disjoint: a vertex off S_X has all its triangles in one
  child by Lemma B1(b), and an open side shared by two triangles of E_X on side s stays in one
  child by (F1).
- **Every piece meets ∂D′.** Every child contains a vertex of S_X. Otherwise, by Lemma B1(b),
  it would be closed under adjacency in R_X, which is connected and meets S_X. So a child with
  one piece touches ∂D′ near that vertex. When a child has several pieces, each contains a
  triangle at a vertex where it is glued. Hence runs(P) ≥ 1 below.

*Boundary sequence.* Walk once around ∂D′ and list the triangles of side s that touch it. At
each vertex of S_X, and at each face node on a virtual closing curve, take its triangles on
side s in rotation order. Each entry belongs to one region; for a child, to one piece.
- **(i) Consecutive entries are adjacent.** At a vertex they share a spoke or an edge e ∉ S_X.
  Between two vertices they are the same triangle t(e, s) of an edge e of S_X, or the same
  triangle along a spoke that the closing curve runs on. So by (F1), consecutive entries of
  different regions are a piece and a hole region.
- **(ii) No crossing.** There are no entries p₁, p₂, p₃, p₄ in cyclic order with p₁, p₃ in a
  piece or hole region A and p₂, p₄ in a different one B.
  - Suppose there were. A and B are disjoint and path-connected.
  - A path in A from p₁ to p₃, closed up by an arc outside D′, is a Jordan curve that
    separates p₂ from p₄.
  - But B joins p₂ to p₄ without meeting it.

*Counting.* A *run* of a region is a maximal cyclic interval of its entries.
- **Claim.** If some hole region has an entry, then Σ (runs(P) − 1) ≤ (number of hole
  regions) − 1, summed over all pieces P.
- **Proof.**
  - Fix an entry p₀ of a hole region H₀. Every piece P has runs(P) − 1 gaps between its runs
    that do not contain p₀. Map each such gap to the region of its first entry, a hole region
    by (i).
  - **The map avoids H₀.** H₀ appears at p₀, outside the gap, and inside the gap. Together
    with P, which appears just before and just after the gap, this is a crossing.
  - **The map is injective.** Suppose two gaps map to the same H. If they are gaps of the same
    P, H appears in both, and P lies between them, which is a crossing. If they are gaps of
    different pieces, then by (ii) the gaps are nested or disjoint. If disjoint, H appears in
    both, which crosses the piece of either gap. If nested, say the gap of P lies inside the gap
    of P′. They start at the same entry only if P = P′. Otherwise H appears at the start of the
    outer gap and again at the start of the inner one, with entries of P between them and after
    the inner gap, which crosses P.
- **No hole region with an entry.** Then by (i) all entries belong to one piece, which has one
  run, and since every piece has an entry it is the only piece on side s.

*Arcs.*
- **One piece.** Each run of a piece maps to a connected part of A_Y. Inside a run, entries at
  one vertex share that vertex, and the step from v to w across an edge e of S_X is the entry
  t(e, s), which makes e an edge of A_Y.
- **The exception.** It is the one run, if any, that runs along a virtual closing curve. A_Y
  has no edge for the virtual edge, so that run may split into two components.
- **A child with m pieces.** Pieces glued at a vertex of S_X share that vertex in A_Y, and the
  pieces of a child are connected through such gluings. So
  a_Y ≤ Σ_k runs(P_k) − (m − 1) + 1 ≤ Σ_P (runs(P) − 1) + 2, summed over all pieces of side s.
- **Result.** By the claim, a_Y ≤ ν(X) + 1 if some hole region has an entry, and a_Y ≤ 2
  otherwise. The final +1 is the exception, so it needs a virtual closing edge. ∎

**Lemma B4.** ν(Y) ≤ ν(X) + 1.

*Proof.* Let C be a component of S² ∖ Ω_Y.
- **C meets a hole of X or D_other.** Suppose C meets neither. C contains no point of S_X: C
  is open, and points of D_other near such a point lie outside Ω_Y ⊆ closure(D_s). So C consists of
  triangles of E_X on side s that are not in Y, together with points they share. The frontier
  of C lies in Ω_Y.
  - An open side on the frontier would be shared by a triangle of C and a triangle of Y. Both
    are in E_X on side s, so by (F1) they lie in the same child, which is a contradiction.
  - So the frontier is finite. But a nonempty open subset of S² with finite frontier is S²
    minus finitely many points, and Ω_Y has triangles. This is a contradiction.
- **Counting.** D_other and every hole of X are connected and miss Ω_Y, so each lies in one
  component C. So there are at most ν(X) + 1 components C. ∎

*Proof of Lemma B1(e).*
- Lemmas B2 and B3 give c(Y) ≤ c(X) + max(1, ν(X)) + 1. With c(root) = 1, ν(root) = 0 and
  Lemma B4, ν ≤ d at depth d, c ≤ 3 at depth 1, and c(X) ≤ 3 + Σ_{i=1}^{d−1} (i + 1) for
  d ≥ 1.
- Every component of T ∩ R_X is a subtree of T, so its diameter is at most 2D.
- A path in T_X meets each component in one subpath, so diam(T_X) ≤ c(X)·2D + c(X) − 1. ∎

### 9.5 What changes in §3 to §6 and Lemma V

Read R_X for G[X] throughout, and "e ∈ R_X" for "e ∈ E(G[X])".
- **Claim 1** is Lemma B1(d). (G1′)'s X_in ⊇ S_X was used only for rule 3, which 3_R replaces.
  There may now be several inside parts, and a separator vertex need not lie in one.
- **Claim 2.** The proof is unchanged, with Lemma B1(b) in place of (7c′).
- **Claim 5.** E^out_X := E(R_X) ∖ λ_d^{-1}(X). In the proof, if u ∉ S_A, then u's child holds
  every side of uw. Since uw ∈ R_X ⊆ R_{A′}, that child is A′.
- **Claim 6(a).** The glued graph is R_X. Every vertex of X has an edge in R_X by definition.
- **Claim 7.** Fix s ∈ S_A and the edges at s labelled A.
  - The inside wedge goes to the one inside part at s.
  - W₁ and W₂ go to O₁ and O₂. Outside chords now follow their half, since 3_R sends them to
    the outside child that holds them.
  - The edges a and b of S_A at s go to the inside part if their inside side is in E_A, and
    otherwise to the adjacent half.
  - So the new labels form at most three cyclic blocks, there are at most 3 label changes at s,
    and |L_A| ≤ 3|S_A|. This improves 8|S_A|.
- **Lemma 15′.** H_X approximates dist_{R_X} on ∂S⁺_X, and leaves gather R_L.
- **Lemma 16′.** The statement is for dist_{R_X}. In the upper bound, the edge from a vertex
  x ∉ S_X lies in x's child by Lemma B1(b), so the prefix of P up to its first vertex of S_X
  lies in R_{X_i}.
- **Lemma V** (NOTES). Let Y be the deepest bag with P* ⊆ R_Y. If Y is not a leaf, then by
  Lemma B1(c) P* meets S_Y. The lower bound uses dist_{R_X} ≥ dist_G. The combinatorial core
  of this form is checked in Lean (`lean/SsspFlow/LemmaVRegion.lean`, no `sorry`, standard
  axioms only): bags with arcs, hubs and kids, and the hypothesis that an arc avoiding the
  hubs lies in one kid.
- **Sizes.** The bounds pick up one more log factor from Lemma B1(e):
  - |S_X| = O(D log² n) and |∂S⁺_X| = O(D log³ n);
  - |N_A| = O(D log² n) and |J_X| = O(D log³ n).

  Labels stay Õ(D/ε).
- **Height.** A child has at most (2/3)|X| + |S_X| vertices, so the height stays O(log n),
  with leaves of size O(D log² n).

### 9.6 Rounds

All bags of one depth run in parallel. A bag communicates over edges of R_X only, mostly
through T_X.
- By Lemma B1(a), every edge carries the traffic of at most two bags per depth.
- By Lemma B1(e), T_X has diameter at most c(X)(2D + 1) = O(D log² n).
- So each per-level step costs Õ(D/ε′) rounds. The steps are:
  - the Γ step of §3.5, including the aggregation and the BFS in T_X for P_X;
  - the transfers of §5 step 1 and of §6;
  - the gathering of R_L at a leaf L;
  - the convergecast of Lemma V.
- The whole tree costs Õ(D/ε′) rounds.

This gives back the Õ(D/ε) of [1, Thm 4] (with Lemmas 14′ to 16′ in place of [1]'s) and the
Õ(D) of Theorem A.

Building the decomposition is local to R_X as well. Every step is flooding, BFS or aggregation
on R_Y over T_Y, whose diameter is at most c(Y)(2D + 1), or the separator of Lemma B5 below:
- the separator S_X, by Lemma B5 on (R_X, T_X), with h at most the diameter of T_X;
- the inside parts and the auxiliary components. A virtual closing edge is not an edge of G.
  Flooding skips it, and the outside children are components of real edges anyway;
- the split at z_s and the components of real edges;
- the connectors, by O(log c(X)) phases of merging over trees of diameter O(D log² n). In each
  phase every part adds the edge of R_Y of smallest ID that leaves it.

Each bag's algorithm sends O(1) messages per edge and round. Lemma B1(a), at depths d and
d + 1, bounds the number of bags that use an edge, so running all bags of one depth in
lockstep costs a constant factor. A level of the decomposition takes O(D log² n log log n)
rounds, the last factor from the connectors.

**Lemma B5 (separator).** Let R be a connected plane graph with n vertices, and T a spanning
tree of R with root r and depth h. Every vertex knows its rotation, its parent and its
children. A deterministic algorithm that uses only edges of R finds, in O(h) rounds and with
O(h) words per edge, vertices y ≠ z and a closing edge yz with these properties:
- yz is an edge of R, or a curve drawn in one face of R from a corner at y to a corner at z;
- the closed curve S = T[y, z] ∪ yz (a cycle, or a digon when yz runs beside a tree edge) has
  at most 2n/3 vertices strictly on each side, and |S| ≤ 2h + 1;
- every vertex knows whether it lies on S or on which side. A vertex of S also knows, for
  each of its corners, edge ends and sides of path edges, the side it faces.

*The tour.* Let N be a thin closed neighbourhood of T. It is a disk, and its boundary γ is a
circle.
- Going once around γ from a point o inside the arc of a corner of r passes every corner of
  R (each along one arc of γ), every end of a non-tree edge, and both sides of every tree
  edge. The two sides of the edge from w to its parent are the *marks* of w, and there are
  2(n − 1) marks.
- Each non-tree edge leaves N at both ends, so outside N it is an arc between two points of
  γ: a *chord*. Chords do not cross. The faces of R are the regions into which the chords cut
  S² ∖ N. A face meets γ in the arcs of its corners and the tree-edge sides between them, and
  it is bounded by these and its chords. So walking around a face visits its corners in
  their order along γ.
- **Marks lemma.** Let κ be a real chord, or a curve drawn in a face from a corner at y to a
  corner at z ≠ y. Let P = T[y, z], C = P ∪ κ, and let α be one of the two arcs of γ between
  the ends of κ. Then exactly (m(α) − |P| + 1)/2 vertices lie strictly on the side of C that
  contains α, where m(α) is the number of marks on α.

  *Proof.* γ meets and crosses C only at the two ends of κ, so the two arcs lie on opposite
  sides of C. Let ℓ be the top vertex of P.
  - A vertex off P has its parent edge off C, so both of its marks lie on its own side.
  - A vertex of P other than ℓ has its parent edge on P, so its two marks lie on the two
    sides.
  - If ℓ ≠ r, the tree path from ℓ to r meets C only at ℓ. So the two marks of ℓ and the
    vertex r, which has no marks, lie on the same side. On that side they contribute 2
    marks for one vertex off P, as every other vertex off P does.

  So m(α) = 2k + |P| − 1, where k is the number of vertices strictly on the side of α. ∎

  The proof also shows which vertices: a vertex w ≠ r off P lies on the side of α exactly
  when its marks lie on α, and r ∉ P lies on the side whose arc contains o.

*Weights.* For such a κ and arc α, let in_α(κ) be the count of the marks lemma and
out_α(κ) := n − |P| − in_α(κ), the count on the other side. For a real chord e, let far(e)
be the arc between its ends that does not contain o, and write in(e), out(e) for the counts
of far(e). Call e *balanced* if in(e) ≤ 2n/3 and out(e) ≤ 2n/3, *heavy* if in(e) > 2n/3, and
*light* if out(e) > 2n/3. A light chord has W(e) := in(e) + |T[e]| < n/3 vertices in the
closed region on its far side. By the remark after the marks lemma, the vertices strictly on
the far side of e are those whose marks lie on far(e); r is never among them.

*The algorithm.*
1. If some chord is balanced, then S is its fundamental cycle, with yz real.
2. Otherwise every chord is heavy or light. If two heavy chords had disjoint far arcs, their
   far sides would have disjoint sets of marks, hence disjoint vertex sets with more than
   4n/3 vertices in total. So the heavy chords are nested. Let e₀ be the innermost one and
   F the face just inside it, or, if there is no heavy chord, F the face of the corner at o.
3. Let y be a vertex with exactly one corner c₀ in F. Walk once around F from c₀ through
   its corners c₁, …, c_m, and let w_j be the vertex of c_j. For c_j with w_j ≠ y, let κ_j be
   a curve in F from c₀ to c_j, and α_j the arc of γ from c₀ to c_j along the walk. Take the
   first j with out_{α_j}(κ_j) ≤ 2n/3, and set z := w_j and yz := κ_j.

*Correctness.* Write in_j and out_j for the counts of κ_j and α_j, P_j := T[y, w_j], and
W_j := in_j + |P_j|.
- **y exists.** Let B be the graph of the edges on the boundary walk of F. If the walk passes
  a vertex v twice, a curve in F between two of its corners at v separates two parts of the
  walk, so v is a cut vertex of B. A connected graph with at least one edge has a vertex that
  is not a cut vertex, and that vertex has one corner in F.
- **No loops.** y has only one corner in F, so w_j ≠ y for every j ≥ 1. Each κ_j joins two
  corners of F and can be drawn inside F.
- **The chords on F.** A chord e ≠ e₀ on the boundary of F has both ends on far(e₀), or
  anywhere if there is no heavy chord, and F lies on its near side. So far(e) is nested in
  far(e₀). Since e₀ is the innermost heavy chord and step 1 found no balanced chord, e is
  light.
- **One step.** Between c_{j−1} and c_j the walk passes one side of a tree edge, or a chord e
  on the boundary of F. In the second case it skips the arc of γ on the side of e away from F.
  That side holds W′ < n/3 vertices in its closed region: W(e) for a light chord, and
  n − in(e₀) for e₀, since in(e₀) > 2n/3. By the marks lemma,
  2 in_j = 2 in_{j−1} + |P_{j−1}| − 1 + m(step) − |P_j| + 1.
  - A side of a tree edge carries one mark, and |P_j| ≥ |P_{j−1}| − 1, so in_j ≤
    in_{j−1} + 1 ≤ W_{j−1}.
  - For a skipped chord e, let d₁ = |P_{j−1}| − 1, d₂ = |T[e]| − 1 and d₃ = |P_j| − 1. By the
    marks lemma m(step) = 2(W′ − |T[e]|) + |T[e]| − 1, so
    2 in_j = 2 in_{j−1} + 2(W′ − d₂ − 1) + d₁ + d₂ − d₃. The triangle inequality d₁ ≤ d₂ + d₃
    in T gives in_j ≤ in_{j−1} + W′ − 1 < W_{j−1} + W′.

  For j = 1 the same computation gives in₁ = 0 or in₁ = W′ − |T[e]| < n/3.
- **Balance.** For the chosen j, out_j ≤ 2n/3. If j = 1 then in₁ < n/3. Otherwise
  out_{j−1} > 2n/3, so W_{j−1} = n − out_{j−1} < n/3, and in_j < W_{j−1} + n/3 < 2n/3.
- **Some j qualifies.** For the last corner c_m, the other side of κ_m is the strict region
  beyond the last step, so out_m = 0 or out_m = W′ − |P_m| < n/3.
- **Size.** S is a path of T plus one edge, so |S| ≤ 2h + 1. ∎

*Rounds.* Each item below is a constant number of convergecasts and broadcasts of O(h) words
over T, or an exchange of O(h) words across a chord. So the algorithm takes O(h) rounds and
carries O(h) words per edge.
- **Tree data.** n, depths, subtree sizes, and every vertex's list of ancestors, of h IDs.
- **Positions.** The tour enters w at a mark and then passes w's corners, non-tree ends and
  child subtrees in rotation order. With the subtree counts, every vertex computes, top down,
  the position on γ of each of its items and the number of marks before it.
- **Chords.** The two ends of a chord exchange positions and ancestor lists, and compute |P|,
  in(e) and out(e).
- **Steps 1 and 2.** One aggregation finds a balanced chord. Otherwise the innermost heavy
  chord is the heavy chord with the largest start. The number of chords whose far arc contains
  a corner is a prefix sum of chord starts and ends along γ, again computed by subtree sums
  and top-down offsets. So every corner knows whether it lies in F.
- **Step 3.**
  - Every vertex counts its corners in F, and an aggregation picks the vertex y of smallest
    ID with exactly one.
  - y broadcasts its position and ancestor list, and every corner of F computes
    |P_j|, m(α_j) and out_j.
  - A minimum over (position − position of c₀) mod |γ| picks j.
- **Output.** Tokens sent up from y and z mark T[y, z], and y and z broadcast the positions of
  the ends of yz. A vertex w ≠ r off S reads its side off the positions of its marks, and r
  takes the side whose arc contains o. A vertex of S reads the side of each of its items off
  its position relative to the two ends of yz.

*Why not [8, Thm 4.4].* [8, Thm 4.4] rests on [14], which is randomized ([9] says so), so
it would not give determinism. There is also a gap in [8]'s write-up. [8, App. B.1] adds
virtual edges A so that the graph becomes biconnected, and then recomputes an embedding of
G ∪ A with [15]. G ∪ A need not be 3-connected, so [8] does not show that this embedding
extends the given one. A separator found in another embedding may be unbalanced, or not
drawable, in the embedding that the regions refer to. A local rule would fix this, since each
A-edge u₁u₂ lies in the corner of its cut vertex u between uu₁ and uu₂. Lemma B5 needs only a
shallow tree, which region bags have by Lemma B1(e), and works in the given embedding.
Deterministic separators for trees of any depth are in [16] and [17]. They would replace
Lemma B5 only if they return a fundamental cycle of the given tree T_X in the given
embedding, which Lemma B2 needs.

**Determinism.** With Lemma B5 every step of the region decomposition is deterministic, given
the embedding and the BFS tree T. The other steps of (L) are deterministic: the Γ step of
§3.5, the oracles and transfers of §5 and §6, and the gathering at leaves. So are Lemma V and
the reduction of [3]. So Theorem A is deterministic, given a deterministic planar embedding
and deterministic face identifiers ((G6); [9, fn. 20] claims a derandomization, [18,
Lemma 3.17] a deterministic version). [17] and [18] use the embedding algorithm of [15] as deterministic; the full text of [15] was
not accessible to us.

### 9.7 Numerical checks (`sim/s9/`)

`engine_r.py` is the region form of the engine of §3.7, `post_r.py` its Lemma 15′ and 16′
checks, and `rsweep.py` the driver. The families and separator modes are those of §3.7.
Closings are straight segments inside one face of G, so these runs never draw a separator
through a hole; the adversarial pass below does.
- **Correctness.** 2,450 instances in seven sweeps, 133,525 bags, no failure:
  - Claims 1 to 7 and (T2) to (T4), including 2.9·10⁸ Monge inequalities;
  - (7a_R), (7c′_R) and contiguity at 47,887 separators;
  - Lemma 16′: 4.95·10⁷ checks;
  - Lemma 15′: 297,798 end-to-end gluings and 3.65 million R1 pairs, with H_X planar in all
    47,887 cases;
  - Lemma V: exact, against Dijkstra from a virtual source with random offsets, at 235,571
    vertices.
- **Property 6_R.** Every edge lay in at most 2 region graphs per depth in every run. In the
  same runs it lay in up to 37 induced subgraphs G[X] per depth (K_{2,m}).
- **Engine fixes.** The adversarial pass found four defects in `engine_r.py`, none in the
  lemmas. All are fixed, and the runs marked *fixed* below use the fixed engine.
  - The crossing test of the virtual candidates had an absolute tolerance, and tiny
    segments between pendant leaves that cross an edge got through. One was used as a
    closing (pend, seed 1328, a bag at depth 5). Candidates are now rechecked exactly.
  - The Jordan check ran over all edges of G, so a closing through a hole would raise a
    false alarm. It now runs over R_X.
  - The hole count merged holes that lie in one face of G, so it could undercount. It now
    counts the components of the missing triangles, adjacent across an edge or a spoke.
  - Claim 7 was checked against the old bound 4 + 2c_s. It now fails above 3 label changes
    per vertex, and Lemmas B3 and B4 now fail a run instead of being counted.
- **Lemma B1(e).** All runs use T_X ⊇ T ∩ R_X and z_s out of the region (faithful, and
  adversarial separators, swaps and degenerate bags).
  - Before the fixes: 3,150 instances, 167,606 child checks. Lemma B2 never failed, and
    a_Y ≤ max(1, ν(X)) + 1 always held with the old hole count, which can only undercount.
  - *Fixed*: 1,750 instances, 88,655 bags, 86,905 child checks with exact ν. Lemmas B2, B3
    and B4 never failed, ν(X) ≤ depth always held, and Claim 7 never had more than 3 label
    changes at a vertex. a_Y exceeded max(1, ν(X)) in 8,230 cases, all with a virtual
    closing edge.
  - *Fixed*, with the full checks of Lemmas 15′, 16′ and V: 140 instances, 7,532 bags, no
    failure.
  - Observed: c(X) ≤ depth + 1 throughout, also on 80 larger instances with n up to 700
    (`big.py`).
- **What the hypotheses do.**
  - With T_X a DFS or random spanning tree of R_X, c(X) reached 41 on grids.
  - With random z_s, a_Y reached 7 with no hole at all.
  - Correctness still held in these runs; only the bound needs [8]'s choices.
- **Lemma B5** (`b5.py`). The algorithm as written, on 4,000 connected plane graphs from all
  sixteen families of this section and of the adversarial pass, n up to 1,842, no failure.
  - *Inputs.* Spanning subgraphs with 0% to 100% of the non-tree edges, so trees and cacti
    occur. BFS, DFS and random spanning trees, with random roots and start corners.
  - *Checks.* Each separator against an independent count: the closing edge inserted into
    the rotations, and each component of R − S given a side by its attachments, which must
    agree. The marks lemma on 66,599 real chords, as ordered sides: the vertices it puts on
    the side of an arc, with the root rule, must be the vertices the count puts there. In
    step 3, that the corners form one whole face, that the walk by face successors is the
    tour order, j = 1 for the first corner, and each step within its bound.
  - *Results.* Step 3 ran in 2,427 instances and step 1 sufficed in 1,573. The larger side
    never exceeded 2n/3, and |S| ≤ 2h + 1 always. A chord step raised in_j by at most
    0.993 W′, so the bound in_j ≤ in_{j−1} + W′ − 1 is nearly tight.
  - *Negative controls* (160 instances each). Without step 2, so that step 3 always walks
    the face of the corner at o, 31 gave an unbalanced chord. With y allowed several corners
    in F, 1 gave a loop.
  - *Adversarial pass* (`sim/attack5/`, 2026-10-29). About 20.8 million instances, with
    an independent implementation of the algorithm and of the side count, compared with
    `b5.py` on every instance. No failure and no disagreement.
    - Exhaustive for n = 4 to 7: every connected planar graph, every planar rotation
      system, every spanning tree, root and start corner (19.4 million instances).
    - All plane trees for n = 7 to 10 (335,000), where step 3 always runs.
    - 1.02 million structured and random instances with n from 10 to 400, in 19 families
      aimed at step 3 (hubs, onions, ears, nested faces, cacti), and 14,400 geometric ones
      with n up to 1,910. Hill climbing on the slack of each step bound.
    - The bounds are reached: the larger side 2n/3 and |S| = 2h + 1.
    - Negative controls (400 each): without step 2, 37 caught; without step 1, 117 caught,
      since the bound W′ < n/3 uses that step 1 found no balanced chord. With y allowed
      several corners in F, none caught; such loops are rare, and `b5.py`'s control found
      1 in 160.
  - B5's closing edges are curves between two corners of one face of R_X. The adversarial
    pass below used 68,323 closings of this kind, so Lemmas B1 to B4 were tested on them.
- **Negative controls** (`neg.py`, 70 instances each):
  - [1]'s rule 3 (separator edges to X_in) in the region form put an owned edge outside its
    bag's region, or broke Claim 1, in 64 of 70 instances;
  - a corrupted Lemma 16′ recursion was detected in 70 of 70;
  - shuffled port orders broke (M) in 70 of 70.
- **Adversarial pass** (`sim/attack4/`). 10,400 instances with 1.7 million vertices,
  1,058,107 bags (391,145 at depth ≥ 8), no violation.
  - *What it adds.* Nine new families (Delaunay with disks removed, sparse Delaunay, rings
    with chords, stacked K_{2,m}, cacti, subdivided Delaunay, grids with holes, spirals,
    wheels of wheels). Greedy separators that aim at the slack of Lemmas B2, B3 and B4 or
    maximize ν or c. Closings through holes: 24,383 straight segments that cross only edges
    outside R_X, and 68,323 combinatorial closings through two corners of one face of R_X.
    Global trees T from DFS and random spanning trees, which Lemma B2 allows. Exact ν,
    computed both as 2 − χ(Ω_X) and as components of the missing triangles; the two always
    agreed.
  - *One aborted instance.* In the run `c1_cb`, one instance (family pend, seed 69) stopped
    on an internal check of the combinatorial closing generator of an earlier engine version,
    before any lemma was checked on it. The same 400 instances, rerun with the published
    engine (`logs/c1r_cb.txt`), pass with no failure and no violation.
  - *Checks.* 1,047,707 child checks of Lemmas B2, B3 and B4, 4.59 million vertex checks of
    Claim 7 (label changes and cyclic blocks), and the claims, (T2) to (T4) and (M) on
    341,722 tiles.
  - *Maxima.* Every edge in at most 2 region graphs per depth; at most 3 label changes and
    3 blocks at a vertex; a_Y − max(1, ν(X)) ≤ 1, and = 1 only with a virtual closing;
    ν(X) ≤ depth; ν(Y) ≤ ν(X) + 1; c(Y) ≤ c(X) + a_Y; c(X) ≤ depth + 1; at most 2 outside
    children per separator vertex.
  - *Tightness.* Lemmas B2, B3 and B4 are each met with equality. For example
    a_Y = 4 = ν(X) + 1 at ν(X) = 3 (swiss, seed 55), ν(Y) = ν(X) + 1 up to ν(X) = 10 (flower,
    seed 6), and c(Y) = c(X) + a_Y with a_Y = 3 (dl, seed 112, c from 2 to 5).
  - *Observed beyond the lemmas.* c(X) ≤ depth + 1 held in every run, even against greedy
    c-maximizers, while c(X) − ν(X) − 1 reached 27, so there is no law c ≤ ν + 1. So the d²
    of Lemma B1(e) is a worst case we never met.

### 9.8 Status of (S9)

- **Proved here.**
  - Lemma B1, the separator of Lemma B5, the parallel schedule (§9.6), and the changes of
    §9.5.
  - So the Õ(D/ε) labels and the Õ(D) of Theorem A follow, given the black boxes of §1.
  - The decomposition is deterministic, and so is Theorem A, given a deterministic planar
    embedding (§9.6).
- **Checked.**
  - A referee pass (2026-10-29) found nothing fatal. Its one serious point, the drawing of a
    virtual closing curve, is now proved in the setting of Lemma B3. Its minor points are in
    (the deviations from [8] in §9.2, the black box in §9.6, the wording in Lemmas B3 and B4).
  - An adversarial pass (2026-10-29) broke no lemma (§9.7). It met Lemmas B2, B3 and B4 with
    equality and found four defects in the test engine, now fixed.
  - Lemma B5 had its own referee pass (2026-10-29): correct as written, with minor gaps and
    wording, now fixed. Its adversarial pass (2026-10-29, §9.7) found no counterexample in
    about 20.8 million instances, among them all instances with n ≤ 7.
  - No human has checked §9.
- **Rating: modest.** It restores the round bounds that (S9) removed. The tools are the
  standard ones: sides of edges, a crosscut argument and a non-crossing count. The
  component bound O(log² n) is weaker than the O(log n) that [8, Def. 4.1 (6)] claims, by one
  log factor, which Õ hides.
