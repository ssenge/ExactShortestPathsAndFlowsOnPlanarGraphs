# Lemma R: the repaired Ĝ_ℓ of Theorem D

*Status (2026-10-29).* Referee pass: correct in substance, no fatal finding. One serious gap:
Fact N below is not stated in [18] and needs its own proof. Minor points: I_ℓ should be
monotone; the host of an incised pair is not free; Table R wording at a degree-1 terminal; Rule
M for edges that leave I_ℓ; R0 against the proof of (5). A revision is in progress. Theorem D
(NOTES.md §5) rests on this lemma.

Theorem D runs Theorem A on the graph Ĝ_ℓ of [18, Thm 3.1]. Read literally, the endpoint
adjustment of [18, Remark 3.3] breaks [18, Thm 3.1 (1), (2)] at s and t (D1 to D3 under
Theorem D in NOTES.md §5). This section defines the repaired graph without reference to code, states the
properties Theorem D needs, and proves them. At s and t the proof is complete. Away from s and t
it cites [18] and argues only the difference.

**Conventions.**
- G is connected and planar, with a fixed rotation system. Parallel edges are allowed. Loops
  are not: a loop crosses no st-cut, so we delete loops first. We have n ≥ 2 and s ≠ t.
- Each edge has two darts. rev δ is the reverse of the dart δ. At a vertex v of degree d, the
  darts leaving v in rotation order are r_v(0), …, r_v(d−1), with indices mod d. pos(δ) is
  the index of δ at its tail.
- The corner c = (v, i) lies between r_v(i) and r_v(i+1). Its in-dart in(c) = rev r_v(i)
  enters v. Its out-dart out(c) = r_v(i+1) leaves v. The edges of r_v(i) and r_v(i+1) are the
  two flanks of c. A dart δ has the tail corner τ(δ) = (tail δ, pos(δ) − 1), which is the
  corner with out(c) = δ, and the head corner η(δ) = (head δ, pos(rev δ)), which is the corner
  with in(c) = δ.
- A face is a cyclic walk of darts in which δ is followed by out(η(δ)). The corner η(δ) lies
  between δ and its successor. So every dart and every corner lies in exactly one face, and
  each face walk alternates darts and corners. The corner (v, i) is the pair (e_i, e_{i+1}) of
  [18].
- P = (p_0, …, p_m) is the simple dual path of Theorem D, with primal edges e_1, …, e_m. The
  edge e_k has p_{k−1} on one side and p_k on the other. m = 0 is allowed; then P has no edges.
- I_ℓ ⊆ E(G) is the set of edges incised at level ℓ: the edges of P and the edges of every
  incised part P_i′ that bounds a level-ℓ annulus ([18, Sec. 3.1], "maps to an incised edge").
  An edge may leave I_ℓ from one level to the next.

**Definition R (repaired Ĝ_ℓ).**

- **R0. Endpoint data (the D3 rule).** For s, choose a corner c*_s = (s, i) that lies in
  p_0. Choose a flank of c*_s that is not in P as the endpoint edge e0. Either e0 is the edge
  of r_s(i), with mode μ_s = L, or e0 is the edge of r_s(i+1), with mode μ_s = R. Mode L is
  preferred when it is legal. The same rule at t, with p_m in place of p_0, gives c*_t, e_last
  and μ_t. Property 5 below shows that a legal choice always exists. Mode L is the copy v_i^L
  of [18, Remark 3.3]. Mode R is the mirrored copy v_i^R, which is not in [18].
- **R1. Tokens and pairs.** A dart δ whose edge is not in I_ℓ has one token (δ, 0). A dart
  whose edge is in I_ℓ has two tokens, (δ, 1) and (δ, 2). The tokens of one edge form pairs:
  {(δ,0), (rev δ,0)} if the edge is unincised, and {(δ,1), (rev δ,2)} and {(δ,2), (rev δ,1)}
  if it is incised. A pair is a level-ℓ copy of the dual edge. Tokens are the copies of an
  edge in [18, Sec. 3.1] and the labelled darts of sim/thmD.
- **R2. Cut structure.** In each face, list the tokens in walk order, with (δ,1) before
  (δ,2). Cut between (δ,1) and (δ,2) for every incised dart δ, and cut at the corners c*_s and
  c*_t. A piece is a maximal run of tokens with no cut inside. It is cyclic if its face has no
  cut. Each token lies in exactly one piece. No piece is empty: c*_s ≠ c*_t, and a corner cut
  and a dart cut never sit at the same place of a walk, so a token lies between any two cuts.
- **R3. Vertices.** For each vertex v of G: a star centre σ(v); a copy D(c) for each corner c
  at v; a copy L(c) when the edge of in(c) is in I_ℓ; a copy R(c) when the edge of out(c) is in
  I_ℓ. In addition, one fresh copy X(c*) for each of c*_s and c*_t.
- **R4. E_R edges.** Each token x is one E_R edge α(x)β(x). Here α(x) is a copy of the tail of
  x's dart and β(x) a copy of its head:
  - (δ,0): α = D(τδ) and β = D(ηδ);
  - (δ,1): α = D(τδ) and β = L(ηδ);
  - (δ,2): α = R(τδ) and β = D(ηδ).

  *Repair (a).* Let c* be a cut corner with mode μ. If μ = L, let x* be the token of in(c*)
  with β(x*) = D(c*), that is (in(c*),0) or (in(c*),2), and set β(x*) := X(c*). If μ = R, let
  x* be the token of out(c*) with α(x*) = D(c*), that is (out(c*),0) or (out(c*),1), and set
  α(x*) := X(c*). We call x* the moved token of c*. It is a token of the endpoint edge.
- **R5. E_S edges.** σ(v)D(c) for each corner c at v, and D(c)L(c), D(c)R(c), D(c*)X(c*)
  when these copies exist.
- **R6. E_C edges.** Each pair π has a host h(π), which is an end of its edge:
  - for an incised edge, the pair {(δ,1), (rev δ,2)} is hosted at the tail of δ;
  - for e0 unincised, the end other than s (this is t when e0 = e_last);
  - for e_last unincised and e_last ≠ e0, the end other than t;
  - for every other unincised edge, the end with the smaller ID.

  For a token x and an end h of its edge, att_h(x) is α(x) if h is the tail of x's dart and
  β(x) otherwise. *Repair (b).* The E_C edge of π = {x, y} is att_h(x)att_h(y), with
  h = h(π). Both of its ends are copies of h.

*Remarks on Definition R.*
- With no moved token, R4 is the E_R formula of [18, Sec. 3.1], and R6 gives its E_C edges
  (u_{j−1}, u_j) and (v_{i−1}, v_i). So the repair changes Ĝ_ℓ only at the copies of s and t.
- The literal reading of [18, Remark 3.3] differs in three ways. (i) When e0 ∈ I_ℓ, e0 is
  treated "just like any other incised edge", so no token moves and Ĝ_ℓ does not cut c*_s
  (D1). (ii) The E_C edge for e0 is always (u_{j−1}, u_j), even when one of these copies has
  lost its token to a cut at u = t (D2). (iii) There is only mode L (D3).
- sim/thmD/thmD.py, build_ghat, variant 'fixed', names X(c*) as L(c*) (mode L) or R(c*)
  (mode R) when e0 ∉ I_ℓ, since those names are free then, and as X(c*) when e0 ∈ I_ℓ. After
  this renaming, an independent builder of Definition R (sim/thmD/repair/formal_ghat.py)
  gives the same edge multiset as build_ghat 'fixed' on every tested level (see *Tests*).
- The host rule of R6 is [18]'s, fixed only to be definite. The proofs of (1) to (6) work for
  any choice of host among the two ends of the edge. The Theorem D notes leave the host of an
  unincised e0 = e_last open; R6 (and sim/thmD) take t.
- Ĝ_0 is Definition R with I_0 = ∅ and without R0: no cut corner, no X, and every face is one
  cyclic piece. This is the Ĝ_0 of [18, Sec. 3.1]. Rule M in (6) uses it at ℓ = 1.

**Fact N (from [18]).** For every level-ℓ annulus A, the token sequence of each node-part of A
is a piece of R2. The pieces that are node-parts of no level-ℓ annulus are called residual.
Every annulus is closed: if a token lies in A, its partner in the pair lies in A too.

Fact N is the combinatorial content of [18, Def. 2.2, Remark 2.5, Def. 2.9, Claims 2.10, 2.12,
2.15], together with the definition of the level-ℓ incised edges in [18, Sec. 3.1]:
node-parts are runs of the face walk, and the incisions in their ancestry cut them inside
incised darts. It is a statement about the annuli, not about Ĝ_ℓ, so the repair does not touch
it. The one exception is the endpoint cut. That cut is introduced at level 1, it is never
undone, and R0 places it at the corner c*_s of s in p_0 (property 5). We also use two facts
from [18]. First, an edge is incised at most once along a chain of ancestors ([18, Lemma 2.6]).
Second, each node-part h of a level-ℓ annulus refines a unique node-part g of the parent
annulus: every token of h is a token of g, or is (δ,1) or (δ,2) where g has (δ,0) ([18, Claim
2.15]). Fact N and closedness are not proved here. They were tested on every node-part of
every live annulus (see *Tests*).

**Lemma R.** Let ℓ ≥ 1, and let the endpoint data satisfy R0. This covers the following
cases:
- e0 or e_last in I_ℓ (D1), including edges that are incised anew at level ℓ and edges that
  leave I_ℓ again;
- e0 = e_last, an st edge, incised or not (D2);
- mode R (D3);
- deg(s) or deg(t) equal to 1 or 2;
- parallel edges;
- an endpoint edge with both darts in p_0;
- m = 0.

The repaired Ĝ_ℓ of Definition R has the following properties.

1. *([18, Thm 3.1 (1)].)* For every piece f, the E_R edges of its tokens form a path p̂(f).
   This is a cycle if f is cyclic. The paths of distinct pieces are vertex-disjoint, and every
   copy except the star centres lies on one of them. By Fact N this holds for every node-part
   f of a level-ℓ annulus. Every vertex of p(f) has a copy on p̂(f).
2. *([18, Thm 3.1 (2), Lemma 3.13].)* The E_C edges are in bijection with the pairs of R1. The
   E_C edge of π = {x, y} joins p̂(f) and p̂(g), where f and g are the pieces of x and y. So
   each dual edge of a level-ℓ annulus has exactly one E_C edge, and it joins the paths of its
   two ends. *Outside the annuli:* every other E_C edge belongs to a pair whose two tokens lie
   in residual pieces. These are the dual edges among the residual node-parts of [18, Cor.
   2.11]: parts left out of the level-ℓ annuli, for instance a side not recursed into after
   the overlap case of [18, Claim 2.3], or a child dropped after [18, Claim 5.8]. No E_C edge
   joins an annulus to a residual piece or to another annulus. An E_C edge is a self-loop only if its host has
   degree 1 and neither token of its pair moved there. It is then a dual self-loop.
3. *([18, Lemma 3.5].)* Ĝ_ℓ is planar. Table R below gives a planar rotation at every copy.
   X(c*) sits in the corner c* that it cuts. Each vertex v of G computes the rotations of its
   copies from its own rotation, from which of its edges are in I_ℓ, from the IDs of its
   neighbours, and from the endpoint data of s and t. All of this reaches v within O(1) rounds.
4. *([18, Lemmas 3.4, 3.15, 3.16].)* The hop diameter of Ĝ_ℓ is at most 4D + 4. A vertex v has
   at most 3 deg(v) + 1 copies, and s and t have at most 3 deg + 2. Once the incisions are
   stored, Ĝ_ℓ is built in O(1) rounds, and a CONGEST round on Ĝ_ℓ takes four rounds on G.
5. *(D3.)* R0 can always be satisfied. s has a corner in p_0, and every such corner has a flank
   that is not in P. In both modes the cut corner is c*_s, which lies in p_0. The same holds
   for t and p_m.
6. *([18, Lemma 3.17].)* The global phase of [18, Lemma 3.17] gives every copy, X(c*)
   included, the IDs of its node-part and of its annulus. The leader of p̂(f) is a copy of a
   vertex of p(f). The local phase is correct with one change: copies are matched across levels
   by tokens (Rule M below), not by name. This replaces the endpoint paragraph of [18, Lemma
   3.17] case 2(c), which is wrong as stated.

**Table R (rotation of the copies).** All lists follow the rotation sense of G.
- σ(v): D(v,0), D(v,1), …, D(v, d−1).
- D(c), for c = (v, i) with a = in(c) and b = out(c): the list σ(v), C_A, A1, A2, B2, B1, C_B,
  with absent entries skipped. C_A is the E_C edge of the pair whose token of a ends at D(c),
  listed only if that pair is hosted at v. C_B is the E_C edge of the pair whose token of b
  starts at D(c), listed only if that pair is hosted at v. These are the E_C edges at D(c)
  across r_v(i) and across r_v(i+1). If deg(v) = 1 they are the two ends of one self-loop. An
  E_C edge rerouted to X(c*) is not listed at D(c*). If a is unincised, A1 is the token of a and A2 is absent. If a is
  incised, (A1, A2) is ((a,2), L(c)) under option (i) and (L(c), (a,2)) under option (ii).
  If b is unincised, B1 is the token of b and B2 is absent. If b is incised, (B1, B2) is
  (R(c), (b,1)) under option (i) and ((b,1), R(c)) under option (ii). At a cut corner the
  moved token's entry is the E_S edge to X(c*).
- L(c) and R(c): two edges each, so the order is immaterial.
- X(c*): (D(c*), C, x*) for mode L and (D(c*), x*, C) for mode R. Here C is the E_C edge of
  the pair of x*, present when that pair is hosted at the vertex of c*.
- Option (ii) is used for exactly one kind of dart: the dart out(c*) of a cut corner c* with
  mode R, when its edge is in I_ℓ. Every other incised dart uses option (i). The option is
  chosen per dart and is the same at both of its ends.

#### Proof

**(5) The D3 rule.** p_0 is a face at s ([18, Alg. 2, line 1]: f ∈ s*), so s has a corner in
p_0. Let c = (s, i) be such a corner, and let A and B be its flanks, the edges of r_s(i) and
r_s(i+1). Both have p_0 on the side of c. An edge e_k of P has p_{k−1} and p_k on its two
sides. P is simple, so e_1 is the only edge of P with p_0 on a side (and there is none if
m = 0). Suppose both flanks were in P. Then A = B = e_1. G has no loops, so r_s(i) and
r_s(i+1) are the same dart, which means deg(s) = 1. Then both sides of e_1 lie in the face of
c, which is p_0. So e_1* is a dual self-loop, and a simple dual path with m ≥ 1 does not use
one. Hence one flank is not in P, and R0 can take it: mode L if A ∉ P, mode R otherwise. If
m = 0, mode L is always legal.

In both modes the cut is at c*_s ∈ p_0. The mode only decides which flank is e0 and which
token moves. So the pieces (R2) and the annuli (Fact N) depend on c*_s but not on the mode.
Under [18, Sec. 5], s may pick any non-P edge e at s with p_0 on one side. If e = r_s(i), then
p_0 contains the corner (s, i) or the corner (s, i−1). R0 reads the first case as mode L at
(s, i) and the second as mode R at (s, i−1). So every choice allowed in [18] has a legal
reading. The formula of [18, Remark 3.3] is the mode-L reading in both cases. In the second
case it cuts (s, i), which lies in the other face of e: this is D3 (run F in sim/thmD). The
argument for t is the same, with p_m and e_m.

**(1) Pieces become disjoint paths.**

*Claim 1 (E_R degrees).* σ(v) has no E_R edge. D(c) carries the in-token of c (the token of
in(c) labelled 0 or 2) and the out-token of c (the token of out(c) labelled 0 or 1). These are
two distinct E_R edges, except at a cut corner, where D(c*) keeps one of them and the moved
token sits at X(c*). L(c), R(c) and X(c*) carry exactly one E_R edge each.

*Proof.* By R4, β(x) = D(c) only for the token of in(c) labelled 0 or 2, and α(x) = D(c) only
for the token of out(c) labelled 0 or 1. Each dart has exactly one such token. Also,
β(x) = L(c) only for (in(c),1), α(x) = R(c) only for (out(c),2), and X(c*) only for x*.
Repair (a) moves x* from D(c*) to X(c*). The darts in(c) and out(c) are distinct, since G has
no loops, and α(x) ≠ β(x) for every token. ∎

*Claim 2 (links).* Let y and z be consecutive tokens of a face walk with no cut between them.
Then they share the copy D(c), where c is the corner between them. Conversely, the two tokens
at any copy with two E_R edges are consecutive in one piece.

*Proof.* The cut between (δ,1) and (δ,2) is always present. So y is the last token of a dart
δ and z the first token of δ′ = out(ηδ), and c = ηδ is not a cut corner. Then y is the
in-token and z the out-token of c, and repair (a) did not move them. By Claim 1, a copy with
two E_R edges is D(c) for a corner c that is not cut, and its tokens are the in-token and the
out-token of c. These are consecutive in the walk of c's face, with no cut between them. ∎

Let f = (x_1, …, x_k) be a linear piece. The edges x_1, …, x_k form the walk α(x_1),
β(x_1) = α(x_2), …, β(x_k). Its interior vertices are the D(c) of the k − 1 corners between
consecutive tokens. These corners are distinct, since a face walk passes each corner once.
The piece starts just after a cut, so α(x_1) carries one E_R edge. After a dart cut, α(x_1)
is R(τδ). After the corner cut c*, α(x_1) is D(c*) (mode L) or X(c*) (mode R). Likewise
β(x_k) carries one E_R edge. So both ends differ from the interior vertices, which carry two.
They also differ from each other: a copy that equals both α(x_1) and β(x_k) carries x_1 and
x_k, so k = 1 and α(x_1) = β(x_1), which is impossible. Hence p̂(f) is a path with k edges
and k + 1 distinct vertices. A cyclic piece is a whole face without cuts. Its tokens close
up into the cycle through the D(c) of all its corners. By Claim 2, paths of different pieces
share no copy. By Claim 1, every copy except σ(·) has an E_R edge, so it lies on exactly one
p̂(f). Every vertex v of p(f) is an end of a dart of f, so the E_R edge of that token ends in a
copy of v. With Fact N this gives [18, Thm 3.1 (1)] for every level-ℓ node-part.

This step replaces [18, Lemma 3.11] near s and t. That proof (l. 1597) treats the endpoint
case "as if v_i had two incident edge copies and one of them got deleted". This fails when
e0 ∈ I_ℓ. In mode L, the piece {(in(c*),2)} then lies between the cut inside in(c*) and the
cut at c*. Under repair (a) its path is the single edge R(τ)X(c*). Without the repair it ends
at D(c*), which also carries the out-token of c*, and the two pieces merge into one path (D1).

**(2) E_C edges.** By R6, every pair gets exactly one E_C edge, and distinct pairs get
distinct edges. So E_C edges correspond one to one to pairs. The copy att_h(x) is an end of
the E_R edge x, so by (1) it lies on p̂(f) for the piece f of x. Hence the E_C edge of
{x, y} joins p̂(f) and p̂(g). If x lies in a node-part of an annulus A, then y lies in A by
closedness, and the pair is a dual edge of A. Conversely, each dual edge of A is such a pair.
If one token of a pair lies in a residual piece, so does the other, by closedness applied to
the other token. This proves (2). For the self-loops: att_h(x) and att_h(y) are copies at the
two corners of h that flank the edge, or X(c*) for a moved token. They coincide only if
deg(h) = 1 and neither token moved at h. Then x and y are consecutive at the single corner of
h, so they lie in one piece.

This step replaces the endpoint paragraph of [18, Lemma 3.13] (l. 1649), which assumes that
the E_C edge (u_{j−1}, u_j) at the other end u is unaffected. That fails when u = t and
e0 = e_last (D2). For the single edge st, (u_{j−1}, u_j) is the self-loop D(t,0)D(t,0). Under
repair (b) the E_C edge is X(c*_t)D(t,0), which joins the pieces {(s→t, 0)} and {(t→s, 0)}.

**(3) Planarity.** We extend the proof of [18, Lemma 3.5]. That proof turns Ĝ_0 into Ĝ_ℓ
through four local steps and leaves the embedding implicit. We give it explicitly.

*Step A: the graph H⁺.* Let H⁺ be Definition R with no moved token and no X, and with, at
every end w of every edge e = r_w(j), the rim edge D(w, j−1)D(w, j). These are the E_C edges
of [18] at both ends of every edge. So H⁺ is the graph after steps 1 to 3 in the proof of
[18, Lemma 3.5], with step 1 adding all rim edges, which that proof allows. We draw H⁺ as
follows.
- Fix a planar drawing of G that realizes its rotation system. Take small disjoint discs B_v
  around the vertices, each meeting only the edges at v, in radial segments. Take thin
  disjoint strips around the edges outside the discs. For a face h, let h° be h minus the discs
  and strips. It is an open disc. Its boundary ∂h° follows the walk of h once: along one side
  of the strip of each dart of h, and along the arc of ∂B_v inside each corner of h.
- Put σ(v) at v and D(c) on the arc of ∂B_v inside c. Each spoke σ(v)D(c) is a radial
  segment.
- The rim edge at v across r_v(i) runs inside B_v from D(v, i−1) to D(v, i). It crosses the
  radial segment of r_v(i) and nothing else. It reaches each of its ends from the side of
  r_v(i).
- An unincised token (δ,0) runs along ∂h° from D(τδ) to D(ηδ), where h is the face of δ.
- An incised dart δ gets a lens: a near arc along ∂h° and a far arc parallel to it inside h°,
  both running from the corner arc of τδ to that of ηδ. Under option (i), the near arc is
  (δ,2), from R(τδ) to D(ηδ), and the far arc is (δ,1), from D(τδ) to L(ηδ). R(τδ) lies on
  ∂h° between D(τδ) and the strip, and L(ηδ) lies just inside h° next to D(ηδ). Under option
  (ii), the near arc is (δ,1), from D(τδ) to L(ηδ), and the far arc is (δ,2), from R(τδ) to
  D(ηδ). Then L(ηδ) lies on ∂h° between the strip and D(ηδ), and R(τδ) just inside h° next to
  D(τδ). The E_S edges D(c)L(c) and D(c)R(c) are short segments.

Nothing crosses. Spokes and rim edges lie inside the discs and meet ∂B_v only at the D(c).
Near arcs lie on the curves ∂h°, which are disjoint for distinct faces, and the near arcs of
one face use disjoint stretches of ∂h°. Far arcs of one face run at one small distance from
∂h°, along disjoint stretches. At a corner c, the entries on the side of in(c) leave D(c)
towards one flank and those on the side of out(c) towards the other. So H⁺ is planar, and
reading the drawing around each copy gives Table R (with both rim edges at every D(c)).

*Step B: the repair. This replaces step 4 of [18, Lemma 3.5].* For each cut corner c* at a
vertex z:
1. Subdivide the E_R edge x* next to D(c*) by the new vertex X(c*). The part between D(c*)
   and X(c*) becomes the E_S edge D(c*)X(c*). In the drawing, X(c*) is a point of the corner
   arc of c*, so it sits in the corner it cuts. Subdivision keeps planarity.
2. If the pair π* of x* is hosted at z, its E_C edge is the rim edge at D(c*) on the side of
   x*: C_A in mode L, where x* is a token of in(c*), and C_B in mode R. In Table R this rim
   edge is next to x* at D(c*). In mode L, x* is A1: the token of an unincised in(c*), or
   (in(c*),2) under option (i). In mode R, x* is B1: the token of an unincised out(c*), or
   (out(c*),1) under option (ii). Option (ii) is used at R-mode corners for exactly this
   reason. So the rim edge can be rerouted along x* to end at X(c*) without crossing anything.
   This is repair (b) at c*. The rotation at X(c*) is then the one in Table R.
3. Delete every rim edge that is not an E_C edge of Definition R. Deleting edges keeps
   planarity.

Each E_C edge of Definition R is a rim edge of H⁺. At most one of its ends is rerouted,
because two moved tokens at one host would need two cut corners at one vertex. The result is
Ĝ_ℓ, so Ĝ_ℓ is planar. The argument does not depend on the host rule. With any host, the kept
E_C edge is a rim edge at that host, and it needs rerouting exactly when its token there
moved.

The two options never conflict. A dart δ needs option (ii) only as out(c*) of an R-mode corner,
which is its tail corner. It would need option (i) at its head only if it were also in(c*′) of
an L-mode corner with δ incised. Then c* = τδ and c*′ = ηδ both lie in the face of δ, so
p_0 = p_m and m = 0. With m = 0 the level-1 annulus is a leaf, and no edge is ever incised.

*Local computation.* Table R at v uses: the rotation at v; which edges at v are in I_ℓ; the
host of each edge at v, which needs the neighbour IDs and whether the edge is e0 or e_last;
whether v is s or t, with its c* and μ; and, for the option at the head of a dart, whether the
dart is out(c*) of an R-mode corner at its tail. s and t send their endpoint data to their
neighbours in one round. So each vertex computes the rotations of all its copies within O(1)
rounds. Theorem A therefore receives an embedding of Ĝ_ℓ that is computed locally from that
of G.

**(4) Diameter, size and simulation.**
- A copy of v is at distance at most 2 from σ(v): D(c) at distance 1, and L, R and X at
  distance 2 through D(c).
- Let e = uv. For a token x of e, the path σ(u), att_u(x), att_v(x), σ(v) has
  3 + (number of ends of x at a leaf) hops. Here a leaf is L, R or X. Unincised tokens have
  D-copies at both ends unless moved. Incised tokens have exactly one leaf end before repair
  (a). Repair (a) moves at most one token of e at s and one at t, and it moves only D-ends.
  - If e is unincised, either one token is moved at both ends and the other token has no leaf
    end, or each token has at most one leaf end. Either way some token gives at most 4 hops.
  - If e is incised, at most two of its four tokens are moved, so an unmoved token gives
    4 hops.

  So d(σ(u), σ(v)) ≤ 4 for every edge uv of G, and the hop diameter of Ĝ_ℓ is at most 4D + 4.
  E_C edges only shorten distances. The bound in [18, Lemma 3.4] is 4D, without the two hops
  at each end.
- v has 1 star centre, deg(v) copies D, at most deg(v) copies L (one per corner with an
  incised in-dart), at most deg(v) copies R, and an X only if v ∈ {s, t}. So
  |V(Ĝ_ℓ)| ≤ 6|E(G)| + n + 2. The bound K = 19n + 1 > |V(Ĝ_ℓ)| of Theorem D survives for
  simple G with n ≥ 3, since 6(3n − 6) + n + 2 = 19n − 34. For a multigraph, merge parallel
  edges first, or take K = |V(Ĝ_ℓ)| + 1 as sim/thmD does.
- Construction ([18, Lemma 3.15]): besides the stored incisions, v needs the index of each
  edge in its neighbour's rotation (one round) and the endpoint data of s and t (one round).
  Copy IDs are v's ID followed by a number in [0, 3 deg(v) + 1].
- Simulation ([18, Lemma 3.16]): E_S edges join copies of one vertex, and by R6 so do E_C
  edges. Each edge of G has at most four tokens, so a round on Ĝ_ℓ takes four rounds on G.
  Repair (a) only changes which copy of s or t holds a token.

**(6) Lemma 3.17 of [18].**

*Global phase.* The global phase of [18, Lemma 3.17] runs connectivity on Ĝ_ℓ[E_R ∪ E_C] and
on Ĝ_ℓ[E_R], with Õ(1) part-wise aggregations on Ĝ_ℓ ([18, Cor. 3.23]). That corollary needs
only (3) and (4). By
(1), the components of Ĝ_ℓ[E_R], apart from the isolated star centres, are exactly the p̂(f)
of the pieces, and X(c*) lies on p̂(f) for the piece f of x*. By (2) and [18, Claim 2.12]
(annuli are connected and disjoint), the component of Ĝ_ℓ[E_R ∪ E_C] that contains p̂(f), for
a node-part f of an annulus A, is the union of the p̂(g) for g ∈ A and the E_C edges of A. So
X(c*) receives the right node-part ID and annulus ID, with no new case. The leader of p̂(f) is
its copy of maximum ID. If that copy is X(c*), the leader vertex is s (or t), which lies in
p(f) because x* is a token of an edge at s. Theorem D uses exactly these outputs: the annulus
of each copy (for the weights and the live test) and the leader copy of p̂(f_i) (for σ).

*Local phase, item 1* (the node-part and annulus of each incident edge). v reads them at the
copy att_v(x), for each token x of an edge at v, X(c*) included. No new case.

*Local phase, item 2* (from level ℓ−1 to level ℓ). The local phase of [18] matches copies by
name (v_i, v_i^L, v_{i−1}^R in Ĝ_{ℓ−1} and Ĝ_ℓ; cases (a) to (c)). We replace this by a rule
on tokens.

*Rule M.* For a level-ℓ token x at v, its parent token x̄ is x if the edge of x is in I_{ℓ−1},
and (δ,0) otherwise, where δ is the dart of x. v declares the node-part of att^ℓ_v(x) in Ĝ_ℓ
to be contained in the node-part of att^{ℓ−1}_v(x̄) in Ĝ_{ℓ−1}.

*Claim 3.* Let x lie in a node-part h of a level-ℓ annulus, and let g be the node-part of the
parent annulus that h refines ([18, Claim 2.15]). Then x̄ is a level-(ℓ−1) token in g, so
att^{ℓ−1}_v(x̄) lies on p̂(g).

*Proof.* By [18, Claim 2.15], every token of h is a token of g, or is (δ,1) or (δ,2) where g
has (δ,0). By Fact N at level ℓ−1, the token of δ in g has a nonzero label exactly when the
edge is in I_{ℓ−1}. If it is, g has (δ,1) or (δ,2), h has the same token, and x̄ = x ∈ g. If
not, g has (δ,0) = x̄. By (1) at level ℓ−1, att^{ℓ−1}_v(x̄) lies on p̂(g). ∎

As a consequence, an edge in I_{ℓ−1} \ I_ℓ has its level-ℓ tokens only in residual pieces: a
node-part h holding (δ,0) would refine a node-part g holding (δ,1) or (δ,2), against [18,
Claim 2.15]. So Rule M never needs a parent for those tokens. Rule M is local, since v knows
I_{ℓ−1}, I_ℓ and the endpoint data, and hence the attachments at both levels. Away from s and t
it reproduces cases (a) to (c) of [18]. At s in mode L (mode R is the mirror image, with R and
out(c*) in place of L and in(c*)), it gives:

| e0 at level ℓ−1, ℓ | copies of s at c* in Ĝ_ℓ, and their match in Ĝ_{ℓ−1} |
|---|---|
| unincised, unincised | X(c*) ↦ X(c*) |
| unincised, incised (incised anew) | X(c*), which holds (a,2), and L(c*), which holds (a,1), both ↦ X(c*), which held (a,0) |
| incised, incised | X(c*) ↦ X(c*); L(c*) ↦ L(c*) |
| incised, unincised | X(c*) lies on a residual piece; no match is needed |
| ℓ = 1 (Ĝ_0 has no X) | X(c*) ↦ D(c*), the copy of x* on the cycle of p_0 in Ĝ_0 |
| any | D(c*) ↦ D(c*) |

Here a = in(c*). In mode R with e0 incised anew, X(c*) holds (b,1) and R(c*) holds (b,2), and
both map to X(c*), which held (b,0), where b = out(c*). This mode-R copy is the mirrored v_i^R
of the D3 rule. In the naming of sim/thmD, the mode-R copy of an unincised e0 is called R(c*),
so there the rule reads "X(c*) and R(c*) ↦ R(c*)".

*The extra case.* The endpoint paragraph of [18, Lemma 3.17] case 2(c) says that the paths of
v_i^L and v_i in Ĝ_ℓ both correspond to the path of v_i^L in Ĝ_{ℓ−1}. Under the repair the
second copy is X(c*), not v_i = D(c*), and D(c*) corresponds to D(c*). In the literal graph,
v_i carries both (a,2) and the out-token of c*. Their node-parts have different parents, so
the stated correspondence is wrong there. This is D1 again.

*Local phase, item 3, and item 4 of [18, Lemma 3.17]* (the parent annulus, and the IDs of all
ancestor node-parts) follow from items 1 and 2 by the argument of [18], unchanged. ∎

#### Degenerate cases

| case | where the proof handles it |
|---|---|
| e0 or e_last in I_ℓ (D1) | R4 moves (in(c*),2) or (out(c*),1) to X(c*). Claim 1 still holds, since L(c*) or R(c*) carries the other token. Step B uses option (i) or (ii). |
| e0 = e_last = st (D2) | E_C edges use att_h (repair (b)). Unincised: one pair, hosted at t, ending at X(c*_t). Incised: each pair is hosted at its own end and may end at X there. |
| e0 incised anew, or leaving I_ℓ | Definition R is per level. Rule M and the remark after Claim 3. |
| mode R (D3) | Mirror image of mode L. Option (ii) at out(c*). |
| deg(s) = 1 | The two flanks of c* are the same edge e0, and in(c*), out(c*) are its two darts. Nothing above assumes distinct flanks. If e0 ∈ I_ℓ, the E_C edge at s is D(c*)X(c*), parallel to the E_S edge. |
| deg(s) = 2 | Two rim edges between D(s,0) and D(s,1), hence parallel E_C edges. |
| parallel edges in G | A 2-gon face gives a 2-cycle p̂ with parallel E_R edges. n = 2 is allowed. |
| e0 with both darts in p_0 | Not excluded anywhere. In [18, Remark 3.3] the other face of e0 is assumed to differ from p_0. |
| m = 0 | p_0 = p_m carries both corner cuts. No edge is ever incised. |

#### Proved and tested

*Proved* (given Fact N, the closedness of annuli, and [18, Lemma 2.6, Claims 2.12, 2.15,
Cor. 3.23]): properties 1 to 6 for every level and every choice allowed by R0, including the
cases in the table above.

*Tested* (sim/thmD/repair/: formal_ghat.py, test_repair.py, witness.py, logs in logs/; they
import sim/thmD/thmD.py unchanged). Run `python3 -I test_repair.py RULE START COUNT [size grid]`
with RULE in formal or anylegal, and `python3 -I witness.py`.
- Definition R was implemented independently of build_ghat, with Table R as an explicit
  rotation system. On every level built by the Reif driver of sim/thmD, the following were
  checked:
  - the edge multiset equals build_ghat 'fixed';
  - V − E + F = 2 and connectivity for Table R;
  - property 1 against the pieces of R2, computed separately;
  - the E_C bijection and ends of property 2;
  - Fact N and closedness for every node-part of every live annulus;
  - d(σ(u), σ(v)) ≤ 4 for every edge of G, and every copy within 2 of its centre;
  - the copy counts;
  - Rule M with Claim 3 against the previous level.
- Runs:
  - 53,000 generated instances (sizes up to 30 and 70, grids up to 12), 140,717 levels, with
    the D3 rule of R0 and with a rule that picks uniformly among all legal (corner, mode) pairs;
  - a further 45,000 instances (114,759 levels) with counters for rare cases;
  - 12 named witnesses (D1, D2 with capacity 0 and 3, n = 2 with three parallel edges, a
    pendant s, a path, C4 twice, K4, a grid with and without pendant terminals, a bridge),
    each run 300 times under each rule.

  In total 98,000 instances and 255,476 levels, plus the witnesses. There were no failures. The
  end-to-end checks of sim/thmD (distances, trees, final cut) also passed on all of these runs.
- Coverage, counted over levels:
  - mode R at about half of the cut corners under the uniform rule (44,934 of 89,798 in the
    last lane);
  - e0 incised in mode L and in mode R (18,842 and 14,329 over all lanes);
  - e0 incised at a degree-1 terminal (1,502) and at a degree-2 terminal (4,217);
  - e0 incised anew (12,133) and leaving I_ℓ again (353);
  - e0 = e_last unincised in all four mode pairs, and incised (129 levels, modes LL and RR
    only). The pairs LR and RL never occur with e0 incised. This matches step B: they would
    put both cut corners in one face, so m = 0;
  - X(c*) of degree 3 (with a rerouted E_C edge) at about 12% of the cut corners.
- Negative controls, 400 instances each: without the option (ii) flip, 80 levels fail Euler;
  with option (ii) on every incised dart, 49 fail; with the two orders at X(c*) swapped, 135
  fail. So each part of Table R is needed.

*Not tested here:* round counts, and [18, Lemma 3.17] as a distributed protocol. Only the
local rule M was checked.

#### Points of doubt

- Fact N is cited from [18], not reproved. It is the one place where the argument away from s
  and t rests on [18]'s Section 2. It held on every tested node-part.
- The planarity proof of H⁺ (step A) describes the drawing in words, sector by sector, not in
  coordinates. Table R was read off that drawing. Its correctness is also checked by Euler's
  formula on every tested level, and the three negative controls show the check is sharp.
- The proof of (5) shows only that R0 is satisfiable and cuts at a corner of s in p_0. It does
  not re-derive that any such corner gives a correct Reif reduction. That rests on [18,
  Remark 3.3] and on the earlier referee pass, as before.
- The multigraph bullet of Theorem D drops E_C self-loops and keeps the lighter of parallel
  E_C edges. Then "exactly one E_C edge per dual edge" holds before that clean-up, not after
  it. Distances are unaffected.
