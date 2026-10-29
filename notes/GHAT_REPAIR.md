# Lemma R: the repaired Ĝ_ℓ of Theorem D

*Status (2026-10-29).* Referee pass (2026-10-29): correct in substance; one serious gap (Fact N)
and the minor points, all addressed in this revision. Adversarial pass (2026-10-29,
sim/thmD/attackR, an independent implementation): no counterexample to Lemma R or Lemma N in
6.9 million exhaustive level-1 corner pairs, 1.3 million Table R builds and 3.5 million
recursion instances (7.7 million levels). It found two wording faults, fixed below (F3 and the
residual sides in (2)), and a defect in the recursion of [18] one step after this lemma, which
RECURSION.md repairs.

Theorem D (NOTES.md §5) rests on this lemma. It runs Theorem A on the graph Ĝ_ℓ of [18, Thm
3.1]. Read literally, the endpoint adjustment of [18, Remark 3.3] breaks [18, Thm 3.1 (1), (2)]
at s and t (D1 to D3 under Theorem D in NOTES.md §5). This section defines the repaired graph
without reference to code, states the properties Theorem D needs, and proves them. Lemma N
first shows that the annuli of [18] are components of a graph on labelled darts. Its proof
takes the structure of one incision step from [18] (facts F1 to F5 below) and proves the rest,
including level 1, where the degenerate endpoint cases are left open in [18].

**Conventions.**
- G is connected and planar, with a fixed rotation system. Parallel edges are allowed. Loops
  are not: a loop crosses no st-cut, so we delete loops first. We have n ≥ 2 and s ≠ t.
- Each edge has two darts. rev δ is the reverse of the dart δ. At a vertex v of degree d, the
  darts leaving v in rotation order are r_v(0), …, r_v(d−1), with indices mod d. pos(δ) is
  the index of δ at its tail.
- The corner c = (v, i) lies between r_v(i) and r_v(i+1). Its in-dart in(c) = rev r_v(i)
  enters v. Its out-dart out(c) = r_v(i+1) leaves v. The edges of r_v(i) and r_v(i+1) are the
  two flanks of c. [18] numbers corners one higher (corner j lies between r_v(j−1) and
  r_v(j)); only the names differ. A dart δ has the tail corner τ(δ) = (tail δ, pos(δ) − 1), which is the
  corner with out(c) = δ, and the head corner η(δ) = (head δ, pos(rev δ)), which is the corner
  with in(c) = δ.
- A face is a cyclic walk of darts in which δ is followed by out(η(δ)). The corner η(δ) lies
  between δ and its successor. So every dart and every corner lies in exactly one face, and
  each face walk alternates darts and corners. The corner (v, i) is the pair (e_i, e_{i+1}) of
  [18].
- P = (p_0, …, p_m) is the simple dual path of Theorem D, with primal edges e_1, …, e_m. The
  edge e_k has p_{k−1} on one side and p_k on the other. m = 0 is allowed; then P has no edges.
- For ℓ ≥ 1, I_ℓ ⊆ E(G) is the set of edges incised before level ℓ: the edges of P and of
  every part P_i′ that [18, Alg. 3, line 17] incised at a level below ℓ. Here P_i′ is the
  maximal subpath of P_i that is internally disjoint from the copies of P ([18, Alg. 3, line
  16]). Edges that P_i′ shares with a path that bounds its annulus are not incised again ([18,
  Remark 2.5]), but they are in I_ℓ already. So I_1 = E(P), I_ℓ ⊆ I_{ℓ+1}, and we set I_0 = ∅.
  An edge is incised at most once ([18, Lemma 2.6]). I_ℓ is the set that [18, Def. 3.2] stores
  (P and the paths computed at earlier levels), so every vertex knows its edges in I_ℓ before
  the subgraphs of level ℓ are built and tested for liveness.
- sim/thmD builds Ĝ_ℓ from a smaller set: E(P) and the edges of the paths that bound the live
  annuli of level ℓ. On every tested level the two sets give the same pieces inside the live
  annuli (see *Tests*). The proofs below use I_ℓ.

**Definition R (repaired Ĝ_ℓ).**

- **R0. Endpoint data (the D3 rule).** s fixes a corner c*_s = (s, i) that lies in p_0 and a
  flank e0 of c*_s that is not in P. If e0 is the edge of r_s(i), the mode is μ_s = L. If e0 is
  the edge of r_s(i+1), the mode is μ_s = R. If deg(s) = 1, both flanks are e0 and either mode
  may be chosen. s sends (c*_s, e0, μ_s) to its neighbours in one round, and the data stay fixed
  for all levels. Any such choice is allowed, and Lemma R holds for each. The same rule at t,
  with p_m in place of p_0, gives c*_t, e_last and μ_t. Property 5 below shows that a choice
  always exists. Mode L is the copy v_i^L of [18, Remark 3.3]. Mode R is the mirrored copy
  v_i^R, which is not in [18]. *Implementation choice:* the rule 'formal' of sim/thmD picks a
  corner of s in p_0 at random among those whose flank r_s(i) is not in P and takes mode L, and
  falls back to mode R only if there is none. The rule 'anylegal' picks uniformly among all
  legal (corner, mode) pairs. Both are instances of R0.
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
  gives the same edge multiset as build_ghat 'fixed' on every tested level with the incised
  set of sim/thmD (see *Tests*).
- The host rule of R6 is [18]'s, fixed only to be definite. For an unincised edge either end
  may host its pair: the E_C edge is a rim edge at both ends (see (3)), and the proofs of (1)
  to (6) do not use which end it is. The Theorem D notes leave the host of an unincised
  e0 = e_last open; R6 (and sim/thmD) take t. For an incised edge the host is forced. Hosted at
  head(δ), the pair {(δ,1), (rev δ,2)} would get the E_C edge L(ηδ)R(τ rev δ), which is not a
  rim edge, and Ĝ_ℓ can be non-planar. A referee probe found this on every level with an
  incision when all incised pairs were moved; its smallest witness moves one pair (seed 54 of
  make_instance, n = 8).
- Ĝ_0 is Definition R with I_0 = ∅ and without R0: no cut corner, no X, and every face is one
  cyclic piece. This is the Ĝ_0 of [18, Sec. 3.1]. Rule M in (6) uses it at ℓ = 1.

#### The token graph and Lemma N

**The token graph.** For ℓ ≥ 1, G*_ℓ is the graph whose nodes are the pieces of R2 and whose
edges are the pairs of R1. The pair {x, y} joins the piece of x to the piece of y. Loops and
parallel edges can occur. G*_0 is G*, with each face as one cyclic piece. The rotation of G*_ℓ
at a piece lists its tokens in walk order. For a linear piece, the *gap* between its last and
first token closes the list into a cycle. This is the embedding that incisions inherit from G*.

A piece is *linear* if its face has a cut, and *cyclic* otherwise. The *ends* of a linear
piece are its first and last token. A token (δ,1) is followed by the cut inside δ, so it is the
last token of its piece, and (δ,2) is a first token. Hence every token of an edge in I_ℓ is an
end of its piece.

We read a node-part of [18] as a run of the walk of its face, that is, as a sequence of
tokens. [18, Def. 2.9] describes a node-part by an interval of the dual edges at a node. A dual
loop at f, which is a bridge of G with f on both sides, occurs twice in that order, once for
each dart. Tokens keep the two occurrences apart. This reading is ours, not one fixed in [18].

**Definition (incision along P).** The level-1 annulus is A_1 := G*_1. In words, the sphere is
cut along the arc γ that leaves s through the corner c*_s into p_0, crosses e_1, …, e_m once
each, and enters t through c*_t. γ has one segment in each face p_k, and the two ends of that
segment are the two cut points of p_k in R2. So p_k splits into two pieces, p_k^0 and p_k^1,
and every other face is one cyclic piece. If m = 0, γ is one segment of p_0 from c*_s to c*_t.
γ is a simple arc, since P is a simple dual path and visits each face once. It meets G only at
s, at t, and once in each e_k.

This agrees with [18, Def. 2.2, Remark 3.3] whenever μ_s = μ_t = L and the other face of e0
(of e_last) differs from p_0 (from p_m). It also covers the cases left open there:
- mode R;
- several corners of s in p_0, where the corner fixes the point at which γ meets s;
- e0 with both darts in p_0, where e0* is a dual loop at p_0;
- deg(s) = 1, where both flanks of c*_s are e0, a bridge with both darts in p_0.

**Facts used from [18].** Let A be a live annulus of level ℓ − 1 ≥ 1 that is not a leaf. Let
P_a and P_b be the incised paths that bound A; near s or t one of them is missing, and at
level 1 both are. In [18, Alg. 3], P_i is computed in A, P_i′ is incised, and some of the
resulting subgraphs are discarded.
- **F1** ([18, Alg. 3, lines 8 and 15 to 17; Remark 2.5]). P_i′ is a simple path in A. Its
  endpoints are node-parts of faces of P, and its internal nodes are not. Its edges that are
  not in I_{ℓ−1} are incised now. The others lie on P_a or P_b and are not incised again.
- **F2** ([18, Def. 2.2, Remark 2.5, proof of Claim 2.10]). Nodes off P_i′ do not change. An
  internal node of P_i′ splits into its parts on the two sides of P_i′, and each newly incised
  edge gets one copy on each side. An endpoint of P_i′ whose edge on P_i′ is newly incised
  splits into two runs that share only that edge; any other endpoint does not change. An
  internal node of P_i′ that an earlier incision split lies on P_a or on P_b.
- **F3** ([18, Claim 5.8; Alg. 3, lines 9 to 19]). A resulting subgraph is discarded if it
  contains an edge of P_a (or P_b) that is not on P_i and is incident to a node of P_i ∩ P_a
  (or P_i ∩ P_b), a bad edge. Two kinds of side get no call either: a side on which P_i meets
  P_a or P_b (the overlap rule of lines 9 to 14), and a side whose index range is empty. The
  remaining subgraphs are the annuli of level ℓ. None of these others is incised again.
  [18, Claim 5.8] states the first sentence as "if and only if", but the converse fails: a side
  can overlap P_a without a bad edge (sim/thmD/attackR, seed 308940). Only the direction stated
  here is used below.
- **F4** ([18, Claim 2.12]). Every annulus is connected.
- **F5** ([18, Lemma 2.6]). An edge is incised at most once. So R1 gives at most four tokens
  per edge.

**Lemma N (annuli are components).** Let ℓ ≥ 1. Every level-ℓ annulus, that is, every annulus
on which ShortestCycle of [18, Alg. 3] is called at depth ℓ, is a connected component of
G*_ℓ. So its node-parts are pieces, its edges are pairs, and it is closed: with a token it
contains the other token of its pair. The other components of G*_ℓ, and their pieces, are
called residual.
Moreover, every piece f of G*_ℓ refines one piece g of G*_{ℓ−1}: for every token x of f, the
parent token x̄ lies in g. Here x̄ = x if the edge of x is in I_{ℓ−1}, and x̄ = (δ,0)
otherwise, where δ is the dart of x.

*Proof.* *Refinement.* Merge (δ,1) and (δ,2) into (δ,0) for every dart δ of an edge in
I_ℓ \ I_{ℓ−1}. This maps the level-ℓ walk of each face onto its level-(ℓ−1) walk, by x ↦ x̄.
Every level-(ℓ−1) cut is a level-ℓ cut, since I_{ℓ−1} ⊆ I_ℓ and the corner cuts are the same
at every level ℓ ≥ 1 (level 0 has none). So a run with no level-ℓ cut inside maps into a run
with no level-(ℓ−1) cut inside.

The rest is an induction on ℓ.

*Level 1.* A_1 = G*_1, so it remains to show that G*_1 is connected. The cases listed above are
outside [18, Claim 2.12], so we prove it.
- Fix a vertex v and an index j, and let δ = r_v(j). The out-token of the corner (v, j−1) is
  the token of δ labelled 0 or 1. The in-token of (v, j) is the token of rev δ labelled 0 or 2.
  By R1 these two tokens form a pair. So consecutive corners of v are joined by pairs. At an
  uncut corner the in-token and the out-token lie in one piece. Hence all pieces that hold a
  token at a corner of v are connected. The cut corner only separates its own in-token and
  out-token, and the chain around v reaches both.
- If e = uv is not in I_1, its token (δ,0) is the out-token of τδ at u and the in-token of ηδ
  at v. This joins the pieces around u to those around v.
- E(P) is the edge set of a simple path of G*. So it contains no cycle of G*, hence no bond of
  G, and G − E(P) is connected.
- Every token is the in-token or the out-token of some corner.

So G*_1 is connected.

*Step from ℓ − 1 to ℓ ≥ 2.* Every level-ℓ annulus is a child of a non-leaf level-(ℓ−1) annulus
A, made by incising Q = P_i′ in A. By induction, A is a component of G*_{ℓ−1}. A new edge of Q,
that is, one not in I_{ℓ−1}, has its pair {(δ,0), (rev δ,0)} in A. So its two new cuts lie in
pieces of A that are nodes of Q. Let g = (x_1, …, x_r) be a piece of A. In A, the two sides of
Q at an internal node g of Q are the two arcs of the rotation of g between the two tokens of
Q at g.

(i) *g is not on Q.* No new cut lies in g, so g is a piece of G*_ℓ, and by F2 it does not
change.

(ii) *g is a cyclic internal node of Q.* Its face has no cut and hence no incised dart, so both
tokens of Q at g are new. The two new cuts split g into two runs, and these are the two sides
of Q at g. Both are pieces of G*_ℓ. No endpoint of Q is cyclic: by F1 it is a node-part of a
face of P, and those faces are cut at level 1.

(iii) *g is an endpoint of Q.* Let z be its token on Q. If z is new, the cut inside its dart
splits g into the run that ends with the first half of z and the run that starts with the
second half. These are the two runs of F2 that share only the edge of z, and both are pieces.
If z is old, no new cut lies in g, and by F2 g does not change.

(iv) *g is a linear internal node of Q.* Let u and w be its two tokens on Q, with u before w
in g.
- The face of g has a cut, so g arose from an earlier incision, and by F2 it lies on P_a,
  say. By F1, g is not a node-part of a face of P, while the endpoints of P_a are. So g is an
  internal node of P_a.
- Every edge of P_a is an edge of P or of P_a′, so it is in I_{ℓ−1}. Hence both tokens of P_a
  at g are ends of g. They are distinct, so they are x_1 and x_r, and both are old.
- The two sides of Q at g are S_in = (u, …, w) and S_out = (w, …, x_r, x_1, …, u), which runs
  through the gap. If u = x_1 and w = x_r, both are old, no new cut lies in g, and g does not
  change.
- Otherwise S_out contains x_1 ≠ u or x_r ≠ w. That token is neither u nor w, since u comes
  before w. So it belongs to an edge of P_a at g that is not on P_i, because P_i meets g only
  in u and w. Since g ∈ P_i ∩ P_a, F3 discards the subgraph that contains S_out.
- S_in starts right after the new cut in the dart of u if u is new. If u is old, it starts at
  x_1 = u, since an old token is an end and u comes before w. S_in ends at w in the same way.
  No cut lies inside S_in, so S_in is a piece of G*_ℓ.

*Pairs.* Pairs of old edges, and of edges not on Q, do not change. Let e be a new edge of Q,
with its dart δ in the node g_1 and rev δ in g_2. In the rotation of A, the sector of g_1 just
before δ is at the corner τδ, and the sector of g_2 just after rev δ is at the corner
η(rev δ). Both are corners of tail(δ) next to e, so both sectors lie on the side of e* at
tail(δ), and hence on the same side of Q. On that side, g_1 keeps the run that ends with (δ,1)
and g_2 the run that starts with (rev δ,2). So the copy of e* on the side of tail(δ) is
{(δ,1), (rev δ,2)}, and the other copy is {(δ,2), (rev δ,1)}. These are the pairs of R1.

*Conclusion.* Let A′ be a level-ℓ annulus, a child of A. By (i) to (iv), its node-parts are
pieces of G*_ℓ, and by the last paragraph its edges are pairs. Each token of a node-part of A′
lies in a pair that is an edge of A′ at that node-part, and the other token of the pair lies
in the node-part at the other end. So the pieces of A′ are closed under pairs, and A′ is a
union of components of G*_ℓ. By F4 it is connected, so it is one component. ∎

**The Reif reduction for every legal corner.** Let λ be the value of a minimum st-cut, and let
d_1 be the distance in A_1 with lengths c. The recursion of [18, Alg. 3] relies on
min_k d_1(p_k^0, p_k^1) = λ. This holds for every choice allowed by R0.
- (≥) Let W be a walk in A_1 from p_k^0 to p_k^1. Draw each pair of W as a curve across its
  edge: across an unincised edge at any point, and for the pair {(δ,1), (rev δ,2)} between
  tail(δ) and the point where γ crosses the edge. Inside a piece, join consecutive crossings
  by a curve on that piece's side of γ. Close W by a curve in p_k that crosses γ once. The
  closed curve crosses γ exactly once and meets G only in edges of W. A closed curve that
  crosses an arc from s to t an odd number of times separates s from t. So every path from s
  to t in G uses an edge of W, and c(W) ≥ λ.
- (≤) A minimum st-cut is a simple dual cycle C that separates s from t ([18, Fact 1.2]). By
  the exchange argument of [18, Claim 2.1], C can be chosen to cross γ only once: between two
  crossings, the part of C is replaced by the part of P between the same faces, which is no
  longer, since P is a shortest path. Cut at that crossing, in a face p_k, C lifts to a walk
  in A_1 from one piece of p_k to the other, of length λ.

Both directions use γ only as a simple arc from s to t that follows P and meets G only at s,
at t and once in each e_k. Every corner of s in p_0 and of t in p_m gives such an arc. So the
reduction is correct for every R0 choice. The exchange step is cited from [18, Claim 2.1];
the rest is proved here.

**Lemma R.** Let ℓ ≥ 1, and let the endpoint data satisfy R0. This covers the following
cases:
- e0 or e_last in I_ℓ (D1), including edges that are incised anew at level ℓ;
- e0 = e_last, an st edge, incised or not (D2);
- mode R (D3);
- deg(s) or deg(t) equal to 1 or 2;
- parallel edges;
- several corners of s in p_0, and an endpoint edge with both darts in p_0;
- m = 0.

The repaired Ĝ_ℓ of Definition R has the following properties.

1. *([18, Thm 3.1 (1)].)* For every piece f, the E_R edges of its tokens form a path p̂(f).
   This is a cycle if f is cyclic. The paths of distinct pieces are vertex-disjoint, and every
   copy except the star centres lies on one of them. By Lemma N this holds for every
   node-part f of a level-ℓ annulus. Every vertex of p(f) has a copy on p̂(f).
2. *([18, Thm 3.1 (2), Lemma 3.13].)* The E_C edges are in bijection with the pairs of R1. The
   E_C edge of π = {x, y} joins p̂(f) and p̂(g), where f and g are the pieces of x and y. So
   each dual edge of a level-ℓ annulus has exactly one E_C edge, and it joins the paths of its
   two ends. *Outside the annuli:* every other E_C edge belongs to a pair whose two tokens lie
   in residual pieces, that is, to an edge of a residual component of G*_ℓ. The residual
   components are the leaves and discarded subgraphs of earlier levels, the subgraphs
   discarded at this level ([18, Claim 5.8, Cor. 2.11]), and the sides that get no call (F3).
   A discarded node-part of [18] can consist of two pieces (S_out in case (iv) of Lemma N).
   No E_C edge joins an annulus to a residual piece or to another annulus. An E_C edge is a self-loop only if its host has
   degree 1 and neither token of its pair moved there. It is then a dual self-loop.
3. *([18, Lemma 3.5].)* Ĝ_ℓ is planar. Table R below gives a planar rotation at every copy.
   X(c*) sits in the corner c* that it cuts. Each vertex v of G computes the rotations of its
   copies from its own rotation, from which of its edges are in I_ℓ, from the IDs of its
   neighbours, and from the endpoint data of s and t. All of this reaches v within O(1) rounds.
4. *([18, Lemmas 3.4, 3.15, 3.16].)* The hop diameter of Ĝ_ℓ is at most 4D + 4. A vertex v has
   at most 3 deg(v) + 1 copies, and s and t have at most 3 deg + 2. Once the incisions are
   stored, Ĝ_ℓ is built in O(1) rounds, and a CONGEST round on Ĝ_ℓ takes four rounds on G.
   I_ℓ is stored before the liveness test of level ℓ, so the construction does not wait for it.
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
  across r_v(i) and across r_v(i+1). If deg(v) = 1 they are the two ends of one self-loop. If
  a is unincised, A1 is the token of a and A2 is absent. If a is incised, (A1, A2) is
  ((a,2), L(c)) under option (i) and (L(c), (a,2)) under option (ii). If b is unincised, B1 is
  the token of b and B2 is absent. If b is incised, (B1, B2) is (R(c), (b,1)) under option (i)
  and ((b,1), R(c)) under option (ii).
- At a cut corner c* at the terminal z, the moved token's entry at D(c*) is the E_S edge to
  X(c*). The end of the rerouted E_C edge that moved to X(c*) is not listed at D(c*): this is
  C_A in mode L and C_B in mode R. If deg(z) = 1, C_A and C_B are the two ends of one rim loop.
  Only the end on the side of x* moves, and the other end stays at D(c*), as C_B in mode L and
  as C_A in mode R.
- L(c) and R(c): two edges each, so the order is immaterial.
- X(c*): (D(c*), C, x*) for mode L and (D(c*), x*, C) for mode R. Here C is the E_C edge of
  the pair of x*, present when that pair is hosted at the vertex of c*.
- Option (ii) is used for exactly one kind of dart: the dart out(c*) of a cut corner c* with
  mode R, when its edge is in I_ℓ. Every other incised dart uses option (i). The option is
  chosen per dart and is the same at both of its ends.

#### Proof

**(5) The D3 rule.** p_0 is a face at s ([18, Alg. 1, line 1, and Alg. 3, line 1]: f ∈ s*; by
[18, Sec. 5], s chooses such a face), so s has a corner in p_0. Let c = (s, i) be such a
corner, and let A and B be its flanks, the edges of r_s(i) and r_s(i+1). Both have p_0 on the
side of c. An edge e_k of P has p_{k−1} and p_k on its two sides. P is simple, so e_1 is the
only edge of P with p_0 on a side (and there is none if m = 0). Suppose both flanks were in P.
Then A = B = e_1. G has no loops, so r_s(i) and r_s(i+1) are the same dart, which means
deg(s) = 1. Then both sides of e_1 lie in the face of c, which is p_0. So e_1* is a dual
self-loop, and a simple dual path with m ≥ 1 does not use one. Hence one flank is not in P,
and R0 can take it, with mode L if it is A and mode R if it is B. If m = 0, both flanks are
legal.

In both modes the cut is at c*_s ∈ p_0. The mode only decides which flank is e0 and which
token moves. So the pieces (R2) and the annuli (Lemma N) depend on c*_s but not on the mode.
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
copy of v. With Lemma N this gives [18, Thm 3.1 (1)] for every level-ℓ node-part.

This step replaces [18, Lemma 3.11] near s and t. That proof (l. 1597) treats the endpoint
case "as if v_i had two incident edge copies and one of them got deleted". This fails when
e0 ∈ I_ℓ. In mode L, the piece {(in(c*),2)} then lies between the cut inside in(c*) and the
cut at c*. Under repair (a) its path is the single edge R(τ)X(c*). Without the repair it ends
at D(c*), which also carries the out-token of c*, and the two pieces merge into one path (D1).

**(2) E_C edges.** By R6, every pair gets exactly one E_C edge, and distinct pairs get
distinct edges. So E_C edges correspond one to one to pairs. The copy att_h(x) is an end of
the E_R edge x, so by (1) it lies on p̂(f) for the piece f of x. Hence the E_C edge of
{x, y} joins p̂(f) and p̂(g). By Lemma N, every level-ℓ annulus A is a component of G*_ℓ. So if
x lies in a node-part of A, then y lies in A as well, and the pair is a dual edge of A.
Conversely, each dual edge of A is such a pair. If one token of a pair lies in a residual
piece, so does the other, since residual pieces form whole components. This proves (2). For
the self-loops: att_h(x) and att_h(y) are copies at the two corners of h that flank the edge,
or X(c*) for a moved token. They coincide only if deg(h) = 1 and neither token moved at h.
Then x and y are consecutive at the single corner of h, so they lie in one piece. If the pair
of x* is hosted at the terminal z of c* and deg(z) = 1, the E_C edge is D(c*)X(c*), parallel
to the E_S edge D(c*)X(c*). This happens for e0 ∈ I_ℓ with deg(s) = 1 (or e_last ∈ I_ℓ with
deg(t) = 1), and for an unincised e0 = e_last with deg(t) = 1.

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
  ∂h° between D(τδ) and the strip of δ, and L(ηδ) lies just inside h° next to D(ηδ), on the
  side of δ. Under option (ii), the near arc is (δ,1), from D(τδ) to L(ηδ), and the far arc is
  (δ,2), from R(τδ) to D(ηδ). Then L(ηδ) lies on ∂h° between the strip of δ and D(ηδ), and
  R(τδ) just inside h° next to D(τδ), on the side of δ. So under both options L(c) lies at the
  corner c on the side of in(c), and R(c) on the side of out(c). Table R depends on this. The
  E_S edges D(c)L(c) and D(c)R(c) are short segments.

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

Each E_C edge of Definition R is a rim edge of H⁺. For an unincised edge this holds with
either end as host: at tail(δ) the E_C edge is D(τδ)D(η rev δ), and at head(δ) it is
D(ηδ)D(τ rev δ), both rim edges. For an incised edge it needs R6: at tail(δ) the pair
{(δ,1), (rev δ,2)} gets the rim edge D(τδ)D(η rev δ), while at head(δ) it would get
L(ηδ)R(τ rev δ), which is not a rim edge of H⁺. At most one end of an E_C edge is rerouted,
because two moved tokens at one host would need two cut corners at one vertex. The result is
Ĝ_ℓ, so Ĝ_ℓ is planar.

The two options never conflict. A dart δ needs option (ii) only as out(c*) of an R-mode corner,
which is its tail corner. It would need option (i) at its head only if it were also in(c*′) of
an L-mode corner with δ incised. Then c* = τδ and c*′ = ηδ both lie in the face of δ, so
p_0 = p_m and m = 0. With m = 0 the level-1 annulus is a leaf ([18, Def. 2.8] and Alg. 2,
line 5: k ≤ j + 1), so no edge is ever incised.

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
- Construction ([18, Lemma 3.15]): besides the stored incisions I_ℓ, v needs the index of each
  edge in its neighbour's rotation (one round) and the endpoint data of s and t (one round).
  Copy IDs are v's ID followed by a number in [0, 3 deg(v) + 1].
- Simulation ([18, Lemma 3.16]): E_S edges join copies of one vertex, and by R6 so do E_C
  edges. Each edge of G has at most four tokens, so a round on Ĝ_ℓ takes four rounds on G.
  Repair (a) only changes which copy of s or t holds a token.

**(6) Lemma 3.17 of [18].**

*Global phase.* The global phase of [18, Lemma 3.17] runs connectivity on Ĝ_ℓ[E_R ∪ E_C] and
on Ĝ_ℓ[E_R], with Õ(1) part-wise aggregations on Ĝ_ℓ ([18, Cor. 3.23]). That corollary needs
only (3) and (4). By (1), the components of Ĝ_ℓ[E_R], apart from the isolated star centres,
are exactly the p̂(f) of the pieces, and X(c*) lies on p̂(f) for the piece f of x*. By (2) and
Lemma N, the component of Ĝ_ℓ[E_R ∪ E_C] that contains p̂(f), for a node-part f of an annulus
A, is the union of the p̂(g) for g ∈ A and the E_C edges of A. So X(c*) receives the right
node-part ID and annulus ID, with no new case. The leader of p̂(f) is its copy of maximum ID.
If that copy is X(c*), the leader vertex is s (or t), which lies in p(f) because x* is a token
of an edge at s. Theorem D uses exactly these outputs: the annulus of each copy (for the
weights and the live test) and the leader copy of p̂(f_i) (for σ).

*Local phase, item 1* (the node-part and annulus of each incident edge). v reads them at the
copy att_v(x), for each token x of an edge at v, X(c*) included. No new case.

*Local phase, item 2* (from level ℓ−1 to level ℓ). The local phase of [18] matches copies by
name (v_i, v_i^L, v_{i−1}^R in Ĝ_{ℓ−1} and Ĝ_ℓ; cases (a) to (c)). We replace this by a rule
on tokens.

*Rule M.* For a level-ℓ token x at v, let x̄ be its parent token as in Lemma N: x itself if
the edge of x is in I_{ℓ−1}, and (δ,0) otherwise, where δ is the dart of x. v declares the
node-part of att^ℓ_v(x) in Ĝ_ℓ to be contained in the node-part of att^{ℓ−1}_v(x̄) in Ĝ_{ℓ−1}.
Since I_{ℓ−1} ⊆ I_ℓ, x̄ is a level-(ℓ−1) token for every x, so the rule is defined everywhere.

*Claim 3.* Let x be a token of a level-ℓ piece f, and let g be the level-(ℓ−1) piece that f
refines (Lemma N). Then att^{ℓ−1}_v(x̄) lies on p̂(g). If f is a node-part of a level-ℓ annulus
A′, then g is a node-part of the parent annulus of A′.

*Proof.* x̄ lies in g by Lemma N, and att^{ℓ−1}_v(x̄) is an end of the E_R edge x̄, which lies
on p̂(g) by (1) at level ℓ − 1. For ℓ = 1, g is a face and p̂(g) its cycle in Ĝ_0. For the
second part, the pieces of A′ arise from those of its parent A by the new cuts of the step in
the proof of Lemma N, so g is a piece of A. ∎

So Rule M is correct for every piece, residual or not. This is [18, Claim 2.15] in token form.
Rule M is local, since v knows I_{ℓ−1}, I_ℓ and the endpoint data, and hence the attachments at
both levels. Away from s and t it reproduces cases (a) to (c) of [18]. At s in mode L (mode R
is the mirror image, with R and out(c*) in place of L and in(c*)), it gives:

| e0 at level ℓ−1, ℓ | copies of s at c* in Ĝ_ℓ, and their match in Ĝ_{ℓ−1} |
|---|---|
| unincised, unincised | X(c*) ↦ X(c*) |
| unincised, incised (incised anew) | X(c*), which holds (a,2), and L(c*), which holds (a,1), both ↦ X(c*), which held (a,0) |
| incised, incised | X(c*) ↦ X(c*); L(c*) ↦ L(c*) |
| ℓ = 1 (Ĝ_0 has no X) | X(c*) ↦ D(c*), the copy of x* on the cycle of p_0 in Ĝ_0 |
| any | D(c*) ↦ D(c*) |

Here a = in(c*). Since I_ℓ is monotone, an incised e0 stays incised. In mode R with e0 incised
anew, X(c*) holds (b,1) and R(c*) holds (b,2), and both map to X(c*), which held (b,0), where
b = out(c*). This mode-R copy is the mirrored v_i^R of the D3 rule. In the naming of sim/thmD,
the mode-R copy of an unincised e0 is called R(c*), so there the rule reads "X(c*) and R(c*)
↦ R(c*)".

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
| e0 incised anew | Definition R is per level, and I_ℓ is monotone. Rule M and its table in (6). |
| mode R (D3) | Mirror image of mode L. Option (ii) at out(c*). |
| deg(s) = 1 | The two flanks of c* are the same edge e0, and in(c*), out(c*) are its two darts. Nothing above assumes distinct flanks. In Lemma N, e0 is a bridge with both darts in p_0. If the pair of x* is hosted at s (e0 ∈ I_ℓ), the E_C edge at s is D(c*)X(c*), parallel to the E_S edge. At t the same happens also for an unincised e0 = e_last with deg(t) = 1, which R6 hosts at t. |
| deg(s) = 2 | Two rim edges between D(s,0) and D(s,1), hence parallel E_C edges. |
| parallel edges in G | A 2-gon face gives a 2-cycle p̂ with parallel E_R edges. n = 2 is allowed. |
| several corners of s in p_0 | R0 fixes one. γ meets s there. Lemma N and the Reif reduction hold for each choice. |
| e0 with both darts in p_0 | e0* is a dual loop at p_0, and tokens keep its two darts apart (Lemma N). In [18, Remark 3.3] the other face of e0 is assumed to differ from p_0. |
| m = 0 | p_0 = p_m carries both corner cuts, and γ is one segment of p_0. No edge is ever incised. |

#### Proved and tested

*Proved*, given F1 to F5 and [18, Claim 2.1, Cor. 3.23]: Lemma N; the Reif reduction at level 1
for every choice allowed by R0; and properties 1 to 6 of Lemma R for every level and every
such choice, including the cases in the table above.

*Tested* (sim/thmD/repair/: formal_ghat.py, test_repair.py, witness.py, logs in logs/; they
import sim/thmD/thmD.py unchanged). Run `python3 -I test_repair.py RULE START COUNT [size grid]`
with RULE in formal or anylegal, and `python3 -I witness.py`.
- Definition R was implemented independently of build_ghat, with Table R as an explicit
  rotation system. On every level built by the Reif driver of sim/thmD, the following were
  checked:
  - the edge multiset equals build_ghat 'fixed' (when both use the same incised set);
  - V − E + F = 2 and connectivity for Table R;
  - property 1 against the pieces of R2, computed separately;
  - the E_C bijection and ends of property 2;
  - the conclusion of Lemma N for every node-part of every live annulus;
  - d(σ(u), σ(v)) ≤ 4 for every edge of G, and every copy within 2 of its centre;
  - the copy counts;
  - Rule M with Claim 3 against the previous level.
- *First round*, with the incised set of sim/thmD (E(P) and the paths that bound the live
  annuli):
  - 53,000 generated instances (sizes up to 30 and 70, grids up to 12), 140,717 levels, with
    the 'formal' and 'anylegal' rules of R0;
  - a further 45,000 instances (114,759 levels) with counters for rare cases;
  - 12 named witnesses (D1, D2 with capacity 0 and 3, n = 2 with three parallel edges, a
    pendant s, a path, C4 twice, K4, a grid with and without pendant terminals, a bridge),
    each run 300 times under each rule.

  There were no failures, and the builder matched build_ghat on every level.
- *Second round*, with the monotone I_ℓ of this revision. A wrapper around test_repair.py
  (test_mono.py and witness_mono.py in sim/thmD/repair/) records every P_i′ that the
  driver incises and rebuilds Definition R from I_ℓ. It ran on 98,000 generated instances
  (260,625 levels) and on the 12 witnesses, 300 runs each under each rule. On 4,569 levels,
  I_ℓ has edges outside the sim's set (10,929 such edges in all). All checks above passed, and
  three more:
  - every live annulus is a whole component of G*_ℓ (320,501 annuli, 3,752,590 node-parts),
    and G*_1 is connected;
  - every piece refines one piece of the previous level, and Rule M holds for every piece,
    residual ones included (2,905,893 pieces);
  - the check of sim/thmD that min_k d_1(p_k^0, p_k^1) = λ, on every run under both rules.

  On the 256,056 levels where the two sets agree, the builder matched build_ghat. There were
  no failures. Since the Lemma N check passed in both rounds, the two sets give the same
  pieces inside every tested live annulus.
- Negative control for monotonicity: with the sim's set instead of I_ℓ, 2,000 instances give
  482 tokens without a parent token and 272 pieces that refine no single parent piece. Both
  lie in residual pieces, where Rule M was undefined before this revision.
- Coverage, second round, counted over levels:
  - mode R at 105,698 of 210,288 cut corners under 'anylegal', and at 20,457 of 114,962 under
    'formal';
  - e0 incised in mode L and in mode R (20,415 and 15,895);
  - e0 incised at a degree-1 terminal (3,585) and at a degree-2 terminal (9,983);
  - e0 incised anew (28,551);
  - e0 = e_last unincised in all four mode pairs, and incised in modes LL (154) and RR (59)
    only. The pairs LR and RL never occur with e0 incised. This matches step B: they would
    put both cut corners in one face, so m = 0;
  - X(c*) of degree 3 (with a rerouted E_C edge) at 40,342 of 325,250 cut corners.
- Negative controls of Table R, 400 instances each: without the option (ii) flip, 80 levels
  fail Euler; with option (ii) on every incised dart, 49 fail; with the two orders at X(c*)
  swapped, 135 fail. So each part of Table R is needed.
- What the Lemma N check shows. sim/thmD models incisions on the same labelled darts (split_seq,
  incise, and the corner cut). So the check validates the bookkeeping of I_ℓ against the
  recursive incision of the driver. It does not test the translation from [18] to tokens; that
  translation is what Lemma N proves.

*Not tested here:* round counts, and [18, Lemma 3.17] as a distributed protocol. Only the
local rule M was checked.

#### Points of doubt

- Lemma N rests on F1 to F5. F2 is taken from the proof of [18, Claim 2.10], not from a
  numbered statement, and F3 is one direction of [18, Claim 5.8]. Both concern one generic
  incision step inside an annulus, away from the endpoint cut. Level 1, the token translation, and the
  cases at linear nodes are proved here.
- The planarity proof of H⁺ (step A) describes the drawing in words, sector by sector, not in
  coordinates. Table R was read off that drawing. Its correctness is also checked by Euler's
  formula on every tested level, and the three negative controls show the check is sharp.
- The multigraph bullet of Theorem D drops E_C self-loops and keeps the lightest of parallel
  edges of any type. Then "exactly one E_C edge per dual edge" holds before that clean-up, not
  after it. Distances are unaffected.
