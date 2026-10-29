# Exact Shortest Paths and Flows on Planar Graphs

This repository contains proofs, machine-checked lemmas and numerical checks for exact
single-source shortest paths (SSSP) and exact maximum flow in planar networks in the CONGEST
model. The main claims are:
- exact directed SSSP in $\tilde O(D)$ rounds (Theorem A), down from $\tilde O(D^2)$;
- exact maximum st-flow in directed planar networks in $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$
  rounds (Theorem C), down from $\tilde O(D^2)$;
- exact minimum st-cut and maximum st-flow value in undirected planar networks in
  $\tilde O(D)$ rounds (Theorem D, new, one referee pass and one adversarial pass; it needs a
  repair at $s$ and $t$ of a construction of [18], proved in Lemma R, one referee pass with one gap being closed), where only a
  $(1-o(1))$-approximation was known in $\tilde O(D)$.

Theorem A depends on the distance labels of the recent preprint [1]. One lemma of [1]
(Lemma 14) is false as stated. This repository shows why and gives a repair. A property of
the decomposition that [1] uses for its round count (Property 6) is also false. We repair
that too, with bags that carry the region they were cut from; see [Status](#status).

## Status

Please read this before relying on anything here.
- The proofs are written up in `notes/`, not yet as a paper. **No human expert has checked
  them.** Every review so far was done by AI agents: a referee pass and an adversarial pass on
  each layer. AI reviewers can share blind spots with the AI that helped write the proofs.
- **Correctness.** Theorems A, B, C and C′ give correct outputs given Lemma 14′, our
  replacement for the false [1, Lemma 14], and the black boxes listed below. Lemma 14′ is
  proved in `notes/LEMMA15.md` §3. A referee pass found it correct given its assumptions,
  and its one serious point is fixed. Two adversarial passes, the second on the fixed text,
  found nothing wrong in it.
- **Round counts: repaired.** [1, Lemma 9 (6)] states that at
  every depth of the decomposition each edge lies in at most two induced subgraphs G[X]. The
  second adversarial pass showed that this is false on $K_{2,m}$ plus one edge, for every
  decomposition with the other properties (`notes/LEMMA15.md`, (S9)). [1] runs all bags of
  one depth in parallel because of this property. Correctness does not depend on it.
  - `notes/LEMMA15.md` §9 replaces $G[X]$ by a *region graph* $R_X$: the edges drawn in the
    part of the plane that bag $X$ was cut from. Every edge then lies in at most two region
    graphs per depth, and the tree components that [8] bounds by $O(\log n)$ are proved to
    be $O(\log^2 n)$.
  - This restores the $\tilde O(D/\varepsilon)$ bound of [1] for the labels and the
    $\tilde O(D)$ of Theorem A. The separator is our Lemma B5, a fundamental cycle found
    with prefix sums along an Euler tour of the shallow tree $T_X$, in $O(D\log^2 n)$ rounds.
    It is deterministic and adds no black box.
  - §9 has had a referee pass, whose fixes are in, and an adversarial pass on 10,400
    instances (about a million bags) that broke no lemma. It found four defects in our test
    engine, all fixed.
  - Lemma B5 has had its own referee pass, correct as written, and an adversarial pass on
    about 20.8 million instances, among them every instance with at most 7 vertices, with no
    counterexample.
- **Theorem D** (2026-10-29) is new. A referee pass found it correct with gaps, now fixed.
  The adversarial pass found that the auxiliary graph $\hat G_\ell$ of [18], as we read its
  Remark 3.3, fails at $s$ and $t$ on small instances (smallest: 4 vertices, minimum cut 2,
  computed 0). A local repair passed 79,000 runs with no failure. Lemma R proves it; a referee
  pass found it correct in substance with one gap, which is being closed.
- **Determinism.** With Lemma B5 the decomposition is deterministic, and so is Theorem A,
  given a deterministic planar embedding and deterministic face identifiers (G6). Both are
  claimed elsewhere, not proved here: [17] and [18] use the embedding algorithm of [15] as
  deterministic (the full text of [15] was not accessible to us), and the face identification
  of [9] is randomized as written, with a one-sentence claim that it derandomizes [9, fn. 20],
  while [18, Lemma 3.17] states a deterministic version. Theorems C′ and D are
  deterministic in the same sense: their other steps are local, use face identifiers computed
  deterministically in [18, Lemma 3.17], or are the deterministic algorithm of [18]. Theorems
  B and C use [6] and hold with high probability.
- Some steps use published results as black boxes; see [What is assumed](#what-is-assumed).

## Background

**The model.** In CONGEST the input graph is the network itself. Every vertex is a processor
that initially knows its incident edges and their weights. Computation proceeds in synchronous
rounds. In every round each vertex can send a message of $O(\log n)$ bits over each incident
edge, and local computation is free. Complexity is the number of rounds, as a function of the
number of vertices $n$ and the hop diameter $D$, which is the diameter of the underlying
undirected, unweighted graph.

Every problem below needs $\Omega(D)$ rounds even on planar networks, since information has to
cross the network. On general graphs, $\tilde\Omega(\sqrt n + D)$ rounds are needed.

**The problems.**
- **SSSP.** Given a source $s$ and integer edge weights of polynomial size, every vertex $v$
  learns $\mathrm{dist}(s,v)$ and its parent in a shortest-path tree. In the directed version
  the two directions of an edge have their own weights.
- **Maximum flow.** Given integer capacities of polynomial size and terminals $s$ and $t$,
  compute the value of a maximum $s$-$t$ flow and the flow on every edge.

**Previous bounds on planar networks.**

| Problem | Upper bound |
|---|---|
| Exact SSSP, directed, $w\ge 0$ | $\tilde O(D^2)$ [8] |
| $(1+\varepsilon)$-approximate SSSP, directed | $\tilde O(D/\varepsilon)$ [1] (preprint) |
| Exact maximum st-flow, directed | $\tilde O(D^2)$ [9] |
| SSSP in the dual graph, negative weights | $\tilde O(D^2)$ [9] |
| Maximum st-flow with $s$, $t$ on a common face | $(1-o(1))$-approximate, undirected, $D\cdot n^{o(1)}$ [9] |
| Maximum st-flow value and minimum st-cut, undirected | $(1-o(1))$-approximate, $\tilde O(D)$, deterministic [18] |

The open question at the end of [9] asks for better primal SSSP, called "the bottleneck to
overcome in order to obtain better distributed planar algorithms", and suggests to "first
improve the $\tilde O(D^2)$ bound of the (easier) directed SSSP problem (even with
non-negative weights)".

## Results

| Result | Rounds | Previous | Rating |
|---|---|---|---|
| Theorem A: exact SSSP, directed, $w\ge0$ | $\tilde O(D)$ | $\tilde O(D^2)$ [8] | modest to solid |
| Theorem B: exact SSSP with negative weights, or a negative cycle | $D\cdot n^{o(1)}$ | $(\sqrt n+D+n^{2/5}D^{2/5})\cdot n^{o(1)}$ on general graphs [6] | modest |
| Theorem C: exact maximum st-flow, directed | $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$ | $\tilde O(D^2)$ [9] | significant |
| Theorem C′: the same with $s$, $t$ on a common face | $\tilde O(D)$ | approximate and undirected only [9], [18] | modest |
| Theorem D: exact minimum st-cut (max-flow value), undirected; new | $\tilde O(D)$ | exact $\tilde O(D^2)$ [9]; $(1-o(1))$-approximate $\tilde O(D)$ [18] | modest to solid |
| Lemma V: distances from a virtual source, and a fix of the query of [1] | $\tilde O(D/\varepsilon)$ | | minor |
| Lemma D: the face-disjoint graph of [9], weighted, realizes dual distances | | | minor |
| [1, Lemma 14] is false | | | modest |
| Property 6 of [1, Lemma 9] is false for induced bags | | | modest |
| Region bags: Property 6 for region graphs, $O(\log^2 n)$ tree components, a deterministic separator | | | modest |
| Lemmas 14′, 15′, 16′: the repair of [1, Lemmas 14 to 16] | | | minor |

All five theorems are conditional (see [Status](#status)): their correctness on Lemma 14′,
and their round bounds also on the region bags of `notes/LEMMA15.md` §9. The ratings in short:
- **Theorem A** closes the planar exact-SSSP gap up to polylogarithmic factors and answers
  the open question of [9]. [18] (2026) still uses approximate SSSP "for the lack of
  almost-D-rounds exact distributed SSSP". The proof is short, though: the reduction of [3], the labels of
  [1], and Lemma V. Since [3, §3.1] already says its boosting works in any model that can run
  its oracle, the theorem is close to folklore once the labels of [1] are available.
- **Theorem B** is a white-box substitution into [6].
- **Theorem C** brings the main theorem of [9] from $\tilde O(D^2)$ to $D\cdot n^{o(1)}$, close
  to the $\Omega(D)$ lower bound. The new term wins once $D$ exceeds $(\log n)^{O(\sqrt{\log n})}$.
  The proof is entirely a composition of known pieces.
- **Theorem C′** is the proof of [9, Thm 1.3] with an exact oracle plugged in.
- **Theorem D** is optimal up to polylogarithmic factors for exact minimum st-cuts in
  undirected planar networks, which [18] leaves open for lack of exact SSSP. The proof puts
  Theorem A into [18], with the weighting of Lemma D. It has had one referee pass so far.
- **The finding about [1, Lemma 14]** is a correctness gap in the main CONGEST result of an
  unrefereed preprint. The repair changes no bound.
- **The finding about Property 6** removes the round bound of the main theorem of [1] as
  written. It also shows that [8, Def. 4.1] together with [8, Lemma 4.3 (8′)] cannot hold on
  a simple family of graphs; [8] describes the intended property for the edges a bag owns,
  which is not refuted.
- **The region bags** restore that bound. The tools are standard (sides of edges, a crosscut
  argument, a non-crossing count), and the component bound is one log factor weaker than
  [8] claims.

### Theorem A (exact SSSP)

**Theorem A.** Let $G$ be a planar digraph with nonnegative integer weights in
$\lbrace 0,\dots,n^{O(1)}\rbrace$, hop diameter $D$ and source $s$. A CONGEST algorithm computes
exact distances from $s$ and a shortest-path tree in $\tilde O(D)$ rounds. The algorithm is
deterministic, given a deterministic planar embedding and deterministic face identifiers
(`notes/LEMMA15.md` §9.6; see [Status](#status)). Local computation is not polynomial: with
the realization theorem [10], which gives existence only, a bag centre finds a realization by
exhaustive search. [1, Thm 1] constructs one in polynomial time, which would make local
computation polynomial; we have not checked that theorem.

The proof has three ingredients.
1. **Reduction.** By [3, Lemma 3.1, Thm 1.7, App. C.1], exact SSSP needs $O(\log^2 n)$ calls to
   an oracle for $(1+\varepsilon_0)$-approximate distances, $\varepsilon_0=\Theta(1/\log n)$.
   The calls run on the same network with new weights, some of them from a virtual source that
   is joined to every vertex with an offset. The reduction is deterministic and costs $O(1)$
   extra rounds per call. Its discretization is only sketched in [3]. Done as written, an update
   can drive a length to $-\eta$, so the base of every update has to be $\ell_i+\eta$ instead of
   $\ell_i$. `lean/SsspFlow/Boost.lean` proves the corrected version.
2. **Labels.** A BDD of height $O(\log n)$ is computed, as in [1] and [8]. For every bag $X$,
   every $v\in X$ learns $(1+\varepsilon)$-approximate distances in $G[X]$ to and from each
   hub of $X$, in $\tilde O(D/\varepsilon)$ rounds [1, Thm 9]. The estimates never
   underestimate. This is where Lemma 14′ enters.
3. **Lemma V** answers the virtual-source queries from the labels.

Two constants handle unreachable vertices and deleted edges, and the tree comes from running
the algorithm on $w'(e)=n^2w(e)+1$. Details are in `notes/NOTES.md` §3.

### Lemma V (virtual source)

**Lemma V.** Given the labels, $(1+\varepsilon)$-approximate distances from a virtual source with
offsets $\varphi$ take $\tilde O(D/\varepsilon)$ rounds.

Every bag $X$ computes $A_X(h)=\min_{u\in X}\varphi(u)+\tilde d_X(u,h)$ for each hub $h$ by a
convergecast. Leaf bags solve their part exactly. Then each $v$ takes the minimum of
$A_X(h)+\tilde d_X(h,v)$ over all bags $X\ni v$ and all their hubs, and of its leaf values.

The minimum has to run over **all** bags that contain $v$. The query in the proof of
[1, Thm 4] uses only the lowest bag that separates the two endpoints, and that is wrong when
the labels store distances in $G[X]$, because a shortest path can leave that bag. A small
counterexample:
- the root separator is $\lbrace a,b\rbrace$, with children $X=\lbrace s,a,b,c,u\rbrace$ and $\lbrace w,a,b\rbrace$;
- $X$ has separator $\lbrace c\rbrace$, with children $\lbrace s,a,c\rbrace$ and $\lbrace u,b,c\rbrace$;
- the arcs are $s\to a$ (1), $a\to w$ (1), $w\to b$ (1), $b\to u$ (1), $a\to c$ (100), $c\to u$ (1) and $s\to c$ (100).

Here $d(s,u)=4$ via $w$, which lies outside $X$, but the query at $X$ returns 101. On random
instances `sim/check.py` finds the single-bag query wrong on about 6% of pairs.

### The gap in [1] and the repair

**What fails.** The labels of [1] come from distance oracles for the bags, built bottom up. At
each bag the hub distances are written as a quasimetric, fitted by a linear program to a cyclic
order of the hubs, and realized by a small planar graph. [1, Lemma 14] provides the cyclic order.
It claims that cutting the bag open along a network of hub paths merges all of its holes into
one face. This fails in three configurations that are consistent with all properties of the
decomposition:
1. **Separator chords.** An edge between two separator vertices, drawn inside the separator,
   splits a hole of a child bag in two. In 58 of 100 random weightings no cyclic order makes
   the linear program feasible, and the worst instance is off by a factor of 1.64.
2. **Virtual closing edges.** When separators close through edges drawn in a face of $G$, the
   cut can disconnect the bag. On a $13\times 8$ grid one vertex then cannot reach another at
   all, although their distance in $G[X]$ is 20.
3. **Holes that touch at one vertex.** The construction adds no path between them, so the two
   holes stay two faces. 53 of 60 weightings have no valid order, and the worst is off by 1.73.

A control run on 300 instances with all hubs on one face gave factor 1 every time, so these
are not artefacts of the linear program. The scripts are in `sim/attack/` (`g2_chord_bfs.py`,
`g2_chord.py`, `g2_virtual.py`, `g2_pinch.py`, and the control `lp_sanity.py`).

**The repair** (`notes/LEMMA15.md`) has two layers.
- **Topological layer: tiles (§3).** A growing set $\Gamma_d$ of corners of $G$ is kept
  connected, as a subgraph of the radial graph. Its faces are the *tiles*, and since
  $\Gamma_d$ is connected, every tile is a disk. Edges are labelled by the bag they belong to.
  Each bag adds new corners where labels change around its separator, along its separator
  path, and if needed along a path to $\Gamma_d$. Nothing is cut. **Lemma 14′** states what
  the analytic layer needs:
  - one label per tile;
  - $O(D\log n)$ new corners per bag and $O(D\log^2 n)$ ports per bag;
  - every tile's piece is drawn in a disk with its ports in boundary order;
  - child tiles glue exactly into their parent tile, and into $G[X]$;
  - every step runs in $\tilde O(D)$ rounds.

  None of the three configurations above can occur with tiles (§3.6).
- **Round count: Property 6.** On $G_m=K_{2,m}$ plus the edge $uw$, every child that receives
  a petal must contain both $u$ and $w$. With separators and leaves of size $O(\log n)$, about
  $n/\log^2 n$ bags of one depth then contain the edge $uw$, not two. Correctness never uses
  this property, but the parallel schedule of [1] does.
- **Region bags (§9).** Every edge has two sides, and each bag $X$ keeps a set $E_X$ of
  sides: the part of the plane it was cut from. Its region graph $R_X$ has the edges with a
  side in $E_X$. The children of $X$ split $E_X$, so every edge lies in at most two region
  graphs per depth (Lemma B1(a)). The separation properties carry over (Lemma B1(b) to
  (d)), and so do §3 to §6 and Lemma V, with sizes one log factor larger.
  - The spanning tree $T_X$ is the BFS tree restricted to $R_X$ plus connectors. Lemma B1(e)
    bounds its components by $3+(d-1)(d+2)/2$ at depth $d$, so its diameter is
    $O(D\log^2 n)$. The proof counts how often a child meets the separator, against the
    holes of the parent's region. [8, Claim 4.6] claims one new component per level, which is
    false (`notes/LEMMA15.md` §1).
  - The separator is Lemma B5. A thin neighbourhood of $T_X$ has a circle as boundary, and
    non-tree edges are non-crossing chords of the outside. The number of vertices on one side
    of a fundamental cycle is read off the number of tree-edge sides along one arc of that
    circle, so all counts are prefix sums along an Euler tour, computed in $O(\text{depth})$
    rounds. If no real fundamental cycle is balanced, a fan of virtual chords inside one face
    finds one, as in the classical planar
    separator theorem. Every other step is flooding or BFS inside $R_X$. We use
    this instead of [8, Thm 4.4], whose proof re-embeds an augmented graph with [15], which
    need not keep the embedding the regions refer to.
- **Analytic layer (§4 to §7).** Lemma 15 of [1] has further gaps, all fixed here:
  - with the witness suggested in the text, the error exponent doubles at every level;
  - the linear program has no triangle constraints;
  - the bit size of the solutions is not controlled;
  - two gluing steps are not proved;
  - unreachable pairs are not handled;
  - one property of the child bags is used without being stated.

  With $\varepsilon'=\varepsilon/(2(3H+1))$, where $H=O(\log n)$ is the height of the
  decomposition, the labels keep size $\tilde O(D/\varepsilon)$.
- **Realization.** In place of [1, Thm 2] we use [10, Thm 1], which is refereed: every
  quasimetric that is Monge for a prescribed circular order is realized by a plane digraph
  with $O(|T|^6)$ vertices and its terminals on the boundary in that order. CONGEST does not
  charge for local computation, so a bag's centre can find such a graph by exhaustive search.
  The proof in [10] is a greedy construction, but [10] bounds the running time only for
  finding the order, not for the construction. Polynomial local time would need that analysis,
  or [1, Thm 2], whose proof does not show the order guarantee.

### Theorem B (negative weights)

**Theorem B.** Let $G$ be a planar digraph with integer weights of polynomial size, possibly
negative, hop diameter $D$ and source $s$. A CONGEST algorithm either computes exact distances
from $s$ or reports a negative cycle, in $D\cdot(\log n)^{O(\sqrt{\log n})}=D\cdot n^{o(1)}$ rounds
with high probability.

[6, Thm 2] reduces the problem to nonnegative SSSP from a virtual source, which Theorem A with
Lemma V solves in $\tilde O(D)$. In [6], the term $\sqrt n+D$ comes only from simulating
minor-aggregation steps. On planar networks these cost $\tilde O(D)$ through low-congestion
shortcuts [9, Cor. 4.6, Lemma 4.8]. Negative cycles are already reported by [6, Thm 60].

### Lemma D, Theorem C and Theorem C′ (maximum flow)

**Lemma D.** Take the face-disjoint graph $\hat G$ of [9, Sec. 3]. It has a star centre for
every vertex, a copy of the vertex for every corner, a cycle $E_R$ through the corners of each
face, one edge $E_C$ per primal edge, and star edges $E_S$. Weight it with 0 on $E_R$, the
dual dart lengths on $E_C$, and a large $M$ on $E_S$. Then $\hat G$ has a negative cycle iff the
dual graph has one, and otherwise distances between corners equal dual distances between their
faces. By [9, Props 1 to 3], $\hat G$ is planar, has hop diameter at most $3D+2$, and every
algorithm on it runs on $G$ with a factor 2 in rounds.

So primal algorithms solve dual distance problems: dual SSSP takes $\tilde O(D)$ with
nonnegative lengths (Theorem A) and $D\cdot n^{o(1)}$ with negative ones (Theorem B). Both were
$\tilde O(D^2)$ [9, Lemma 2.2]. The weights on $E_C$ are already in [9, Prop. 5]; the new parts
are the weights on $E_R$ and $E_S$ and running primal algorithms on the result.

**Theorem C.** Let $G$ be a directed planar network with integer capacities in
$\lbrace 0,\dots,\mathrm{poly}(n)\rbrace$ and terminals $s,t$. A CONGEST algorithm computes a maximum
st-flow, its value and the flow on every edge, in $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$
rounds with high probability.

The proof is the reduction of [11] as used in [9, Sec. 6.1]: a binary search on the flow value,
where each step is a dual negative-cycle test, now done with Lemma D and Theorem B. A minimum
cut follows from reachability in the residual graph, in $\tilde O(D)$.

**Theorem C′.** If $s$ and $t$ lie on a common face, the maximum st-flow is computed exactly in
$\tilde O(D)$ rounds for directed networks, deterministically given a planar embedding. This
is the method of [12]:
add a chord between $s$ and $t$ inside the face and compute one dual SSSP with nonnegative
lengths. [9, Thm 1.3] gives a $(1-o(1))$-approximation for undirected networks in
$D\cdot n^{o(1)}$ rounds, and [18] one in $\tilde O(D)$ rounds for any $s$ and $t$.

### Theorem D (exact minimum st-cut, undirected)

**Theorem D.** Let $G$ be an undirected planar network with integer capacities of polynomial
size and terminals $s,t$. A CONGEST algorithm computes the value of a minimum st-cut, which is
the maximum st-flow value, in $\tilde O(D)$ rounds; every vertex learns its side and its cut
edges. It is deterministic given the embedding algorithm of [15], as in [18], and
deterministic face identifiers (G6). The proof has had
one referee pass (correct with gaps, all fixed) and one adversarial pass (below).

[18] computes a $(1+o(1))$-approximate minimum st-cut with Reif's algorithm: $O(\log n)$
levels of incisions in the dual, each with $O(1)$ rounds of SSSP, one source per annulus. Its correctness argument
[18, Lemma 2.7] holds unchanged with exact shortest paths, so only the SSSP step needs
replacing. [18] runs approximate SSSP on each annulus through minor aggregation, because
annuli can have large diameter. We instead run Theorem A on the whole graph $\hat G_\ell$ of
[18, Thm 3.1], which is planar, has hop diameter at most $4D+4$ (from the bound $4D$ between
star centres of [18, Lemma 3.4]) and is simulated on $G$ with
four rounds per round. Its weights are 0 on the paths that represent dual nodes,
$K\cdot c(e)+1$ on the edges that represent dual edges of live annuli, and a large $M$ on all
other dual edges and on the star edges between copies of a vertex, from a virtual source with
one zero-weight arc per annulus. As in
Lemma D, distances below $M$ are exact annulus distances, and the $+1$ breaks ties so that
the parent choices form shortest-path trees. Details are in `notes/NOTES.md` §5.

**The endpoint repair.** [18, Remark 3.3] adjusts $\hat G_\ell$ at $s$ and $t$ through two
edges $e_0$ and $e_{\text{last}}$ next to the first and last dual nodes of the first cut path.
Read literally, it breaks [18, Thm 3.1 (1), (2)] in three ways, found by the adversarial pass
in `sim/thmD/`:
- If a later incision passes through $e_0$, Remark 3.3 treats it like any other incised edge.
  The corner of $s$ that was cut is then joined again, two dual nodes share one path in
  $\hat G_\ell$, and their distance becomes 0. Smallest witness: vertices 0 to 3, edges
  $\lbrace 0,3\rbrace,\lbrace 0,1\rbrace,\lbrace 1,2\rbrace,\lbrace 2,3\rbrace$ with capacity 1 and
  $\lbrace 3,1\rbrace$ with capacity 5, $s=1$, $t=2$: minimum cut 2, computed 0.
- If $e_0=e_{\text{last}}$ is an edge $st$, the dual edge $e_0^*$ is wired to the wrong copies
  (one edge $st$ of capacity 3: distance 29 instead of 22).
- [18, Sec. 5] lets $s$ take any edge outside the path as $e_0$, but the formula needs one
  particular edge, which in about 30% of instances lies on the path; then we use the
  mirrored copy.

The repair: an incised $e_0$ attaches on the cut side to a fresh copy of $s$ (and likewise
$e_{\text{last}}$ at $t$), and each dual edge joins the copies its two path edges actually
attach to. It is local at $s$ and $t$ and adds at most two vertices. The repaired graph passed
79,000 runs on 64,000 instances with exact distances, trees and cut values; every one of 1,848
graphs built for a planarity check was planar with hop diameter at most $4D+4$. The literal
graph failed in about a third of the instances. Lemma R (`notes/GHAT_REPAIR.md`, 2026-10-29)
defines the repaired graph formally and proves what Theorem D needs from it: the properties
[18, Thm 3.1 (1), (2)], planarity with an explicit rotation at every copy, the diameter bound,
and the local phase of [18, Lemma 3.17]. An independent implementation of its definition
matched the tested graph on 98,000 instances. A referee pass found Lemma R correct in
substance, with one serious gap: a description of the dual nodes that it cites from [18] is not
stated there and needs its own proof. A revision is in progress. These failures may come from a misreading of [18] on our side.
We have not checked whether they affect the approximate algorithm of [18].

## What is assumed

Beyond the results cited in the proofs, these enter as black boxes:
- **(G1) The decomposition** of [1, Lemma 9], as built in [8, Sec. 4.2]. We use the shape of
  its child bags as we read it off [8], and spanning trees of diameter $O(D\log n)$ per bag.
  [1] states height $O(D)$, which [8] does not give; the difference costs one log factor.
  This is needed only for the induced form of the labels (`notes/LEMMA15.md` §3 to §6). The
  final theorems use the region decomposition of §9, which is constructed and analysed there;
  its height bound and bag identifiers are only sketched.
- **(G3) Realization**, [10, Thm 1]. It gives existence only, so a bag centre searches
  exhaustively, which takes exponential local time (CONGEST does not count it).
- **(G4)** Distances in a graph drawn in a disk satisfy the Monge condition in boundary order.
  This is standard, and the notes give the proof.
- **(G5) Distance oracles** for planar digraphs [13], as used in [1, Lemma 11].
- **(G6) Face identifiers** in $\tilde O(D)$ rounds [9, Lemma 5.11].

## Machine-checked proofs (`lean/`)

Lean 4 (`leanprover/lean4:v4.36.0-rc1`) with Mathlib; the exact Mathlib revision is pinned in
`lean/lake-manifest.json` and in `lean/lakefile.toml`. All theorems depend only on the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry`.
`lake env lean SsspFlow/Axioms.lean` prints the axioms of every named theorem; its output is in
`lean/axioms.txt`. In a fresh clone, run
`lake exe cache get` before `lake build`, or Lake compiles all of Mathlib from source.

- `lean/SsspFlow/LemmaV.lean`, theorem `SsspFlow.Hierarchy.lemmaV`: Lemma V for an abstract bag
  hierarchy with arc lengths in $[0,\infty]$, distances as infima over walks, and estimates
  within $1+\varepsilon$ of the distances in each bag. The hypotheses on the hierarchy follow
  from the decomposition's separation property. No finiteness is assumed.
- `lean/SsspFlow/LemmaD.lean`: Lemma D.
  - `Setup.negCycle_iff`, `Setup.walks` and `Setup.lemmaD` prove it for any graph with the
    face-cycle, dual-dart and star structure of $\hat G$; parallel arcs and loops are allowed.
  - `rotSetup` builds $\hat G$ from a combinatorial map, `rot_pair` shows that both arcs of an
    edge join the same two corners, and `rot_lemmaD` is Lemma D for that graph.
  - Planarity is never used, so the weighting works on any surface.
- `lean/SsspFlow/Tools.lean`: tools of the repair of [1], with walks in multidigraphs and
  "for every walk on one side there is a walk on the other side at most $\lambda$ times as
  long" as the form of $\mathrm{dist}\le\lambda\cdot\mathrm{dist}$.
  - `glue`: the combinatorial core of Lemma R1 (gluing keeps terminal approximation). A walk
    between terminal images cuts into segments of one piece with no terminal image inside
    (`decomp`). The quotient construction is not formalized; its properties are hypotheses.
  - `rounding`: Lemma R6 (capping and rounding up to multiples of $\eta$ costs at most a factor
    $1+\varepsilon$ when $\eta\cdot|V|\le\varepsilon$ and distances are at least 1), with
    `rnd_bounds` for the new weights.
  - `level_step`: the factor $(1+\varepsilon')^3$ per level of Lemma 15′.
  - `params`: $(1+\varepsilon/(2(3H+1)))^{3H+1}\le 1+\varepsilon$ for $\varepsilon\in[0,1]$.
- `lean/SsspFlow/Labels.lean`, theorems `SsspFlow.labelOut` and `SsspFlow.labelIn`: one level
  of Lemma 16′ in both directions, for induced bags (distances inside vertex sets). The
  separation property of the child bags enters as a closure hypothesis on arcs. The region
  form of Lemma 16′ is not formalized.
- `lean/SsspFlow/Boost.lean`, theorem `SsspFlow.Boost.Run.exact`: the discretized boosting of
  [3] with base $\ell_i+\eta$. Lengths stay nonnegative (`Run.len_nonneg`), every vertex
  contracts by a factor $1-1/\alpha$ up to an additive $(n-1)\eta$, and the final rounding is
  exact once the stated bounds hold. `c1_negative` is the one-arc instance where base $\ell_i$
  gives $-\eta$.

- `lean/SsspFlow/LemmaVRegion.lean`, theorem `SsspFlow.RHierarchy.lemmaV`: Lemma V for region
  bags. Bags carry arc sets, and an arc of a bag between two non-hubs lies in a common child.

Not formalized: the CONGEST algorithms and their round counts, planarity and the diameter
bound of $\hat G$, the decomposition, Lemma 14′ and everything else in the repair that uses
planarity (Lemmas R3, R5, R7, and the Monge condition).

## Numerical checks (`sim/`)

Requires Python 3 with `numpy`, `scipy` and `networkx`. Run each script from its own directory.
These scripts test finite families and the sequential meaning of the statements. They do not
test round counts.

- `sim/check.py`: Lemma V, Lemma D, Theorem C and Theorem C′ on random planar instances, in exact
  arithmetic. `python3 check.py 40 1` runs 40 instances with seed 1.
- `sim/tiles/tiles2.py`: the tile construction of Lemma 14′ as written, with child bags shaped
  as in [8]. It checks every claim of §3 per level, the Monge condition on every tile, and the
  planarity of every gluing. Run as `python3 tiles2.py <seeds> [virtual|neg|pend3|pend6]`.
  `tiles.py` is the first version. The `run*.txt` files hold the outputs listed in
  `notes/LEMMA15.md` §3.7: about 2.7 million Monge checks and no failure, while the negative
  controls fail as they should.
- `sim/ref2/`: the referee's independent check of §3. `walk_check.py` rebuilds the boundary
  order of every tile from port records alone, as the distributed algorithm would, and
  `pendant.py` builds the graphs that exposed the problem with the earlier child shape.
- `sim/attack2/`: the adversarial pass on the earlier draft of §3. It ran 24,850 instances on
  15 families, with $1.55\cdot 10^9$ Monge inequalities, and found no failure under that
  draft's assumptions. `run.py` is the driver, `engine.py` the construction and its checks,
  and `s7_rebuild.py` rebuilds the three configurations above. `g1_inconsistency.py` shows that
  one child per outside component is incompatible with the decomposition's properties on
  stars. `g1_grouped.py` repeats that search with the grouping of [8] and finds balanced
  children.
- `sim/attack3/`: the second adversarial pass, on the fixed text: 14,500 instances with no
  failure in Lemma 14′ or in the parts of Lemmas 15′ and 16′ that use it, with negative
  controls. `p6.py` builds the family on which Property 6 fails
  (`python3 -I p6.py 100 u 8 nopost`), and `lp46_demo.py` a step of [8] that adds more than
  one tree component. `sweep.py` and `run.py` drive the sweeps; `logs/` holds their output.
- `sim/s9/`: the region bags of §9. `engine_r.py` is the region form of the engine,
  `post_r.py` its Lemma 15′ and 16′ checks, `rsweep.py` the driver, `big.py` larger
  instances, and `neg.py` the negative controls. 2,450 correctness instances had no failure,
  and every edge lay in at most two region graphs per depth. With `NOSPLIT=1` the engine never
  splits a separator vertex; 1,400 instances of that form also had no failure. After the fixes from the
  adversarial pass, 1,750 instances checked Lemmas B2 to B4 with exact hole counts at 86,905
  children without a violation (`logs/e_*.txt`); `logs/` holds all output. `b5.py` runs
  Lemma B5 and checks each separator against an independent side count (4,000 instances, n
  up to 1,842, no failure; `python3 -I b5.py START END`).
- `sim/attack5/`: the adversarial pass on Lemma B5. `mine.py` is an independent
  implementation with its own side count, and `harness.py` compares it with `b5.py`.
  `exh.py` and `exh_trees.py` enumerate all instances for small n, `rand.py`, `fams.py` and
  `geo_cmp.py` run larger ones, `hill.py` climbs towards the step bounds, and `negctl.py`
  runs the negative controls.
- `sim/thmD/`: the adversarial pass on Theorem D. `thmD.py` runs Reif's algorithm as in [18],
  driven only by the exact trees of Theorem D, on the literal and the repaired $\hat G_\ell$,
  and checks every distance, tree and final cut against networkx. `minimize.py` shrinks
  failures, `planar_check.py` tests planarity and diameter, and `lane1.sh`/`lane2.sh` give the
  runs. `logs/summary.txt` sums them up. `repair/` checks Lemma R: `formal_ghat.py` builds
  the repaired graph from its written definition, and `test_repair.py` and `witness.py`
  compare it with `thmD.py` and check its properties.
- `sim/attack4/`: the adversarial pass on §9. `engine_r9.py` adds exact hole counts,
  closings through holes, greedy separators that aim at the slack of Lemmas B2 to B4, and
  other global trees; `engine_c9.py` draws closings combinatorially; `fams9.py` adds nine
  families (Delaunay with holes, sparse Delaunay, cacti, wheels of wheels and others). Run
  `python3 -I adv.py CONF A:B fam1,fam2 SCALE`. `tight.py` finds the equality cases.
- `sim/attack/`: the counterexamples to [1, Lemma 14], and checks of the analytic layer:
  gluing (`r1_glue.py`), rounding (`r6_round.py`), the error recursion (`l16.py`), the squaring
  in [1, Thm 2] (`s1_square.py`), and the first adversarial runs on Lemma V and Lemma D
  (`lemmaV.py`, `lemmaD_flow.py`). `rot.py` is a small rotation-system library used by the
  others.
- `sim/ref/monge.py`: an instance that satisfies the Monge constraints of [1] for one linear
  reading of the order but not for the circular one, which is why the notes impose them in all
  rotations.

## Notes (`notes/`)

- `notes/NOTES.md`: the state of the art, Theorems A, B, C, C′ and D, Lemmas V and D, the
  ratings, and the review history.
- `notes/GHAT_REPAIR.md`: Lemma R, the repaired auxiliary graph of [18] that Theorem D runs on.
- `notes/LEMMA15.md`: the gaps in [1, Lemmas 14 to 16] and their repair, with Lemma 14′ (§3),
  the analytic layer (§4 to §7), what is settled (§8), and the region bags that repair the
  round count (§9).

These are working notes. References such as "lty 1762", "adpw 2166" or "adw26 1673" point to
line numbers in plain-text extractions of [1] (arXiv v2), [9] and [18].

## Open questions

- Directed planar global minimum cut is at $\tilde O(D^2)$ [9, Thm 1.5]. It needs the shortest
  cycle of simple darts in the dual. $\hat G$ has cycles of weight 0, so the girth of
  $\hat G$ does not give it.
- Weighted girth of planar digraphs, also at $\tilde O(D^2)$ [19]. If its algorithm uses
  polylogarithmically many exact SSSP calls, Theorem A may improve it; we have not checked.
- Can the $n^{o(1)}$ in Theorem C be removed? That needs a reduction for negative weights with
  polylogarithmic overhead.
- Is the component bound of Lemma B1(e) really $\Theta(\log^2 n)$? All runs stayed at
  depth + 1.
- Theorems A, C′ and D are deterministic given an embedding. Are Theorems B and C? That
  needs a deterministic version of [6].
- Can the realization step run in polynomial local time? [1, Thm 1] claims a polynomial-time
  construction; we have not checked it.
- A maximum st-flow assignment in undirected planar networks in $\tilde O(D)$. Theorem D
  gives the value and a minimum cut; [18] asks for the assignment as well.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to search the literature, to
develop and check the proofs, to run the referee and adversarial passes, to write the scripts
and the Lean formalization, and to draft the text.

## References

The numbers match those in `notes/`.

1. H. Le, H. Tierno, S. Yang. Planar Embedding of Okamura-Seymour Quasimetrics in Polynomial
   Time with an Application to Distributed SSSP. arXiv:2606.31192 (v2, 2026).
2. N. Cao, J. T. Fineman. Parallel Exact Shortest Paths in Almost Linear Work and Square Root
   Depth. SODA 2023.
3. V. Rozhoň, B. Haeupler, A. Martinsson, C. Grunau, G. Zuzic. Parallel Breadth-First Search
   and Exact Shortest Paths and Stronger Notions for Approximate Distances. STOC 2023,
   arXiv:2210.16351.
4. S. Chechik, D. Mukhtar. Single-source shortest paths in the CONGEST model with improved
   bounds. PODC 2020.
5. N. Cao, J. T. Fineman, K. Russell. Brief announcement: an improved distributed approximate
   SSSP algorithm. PODC 2021.
6. V. Ashvinkumar et al. Parallel, Distributed, and Quantum Exact SSSP with Negative Edge
   Weights. ESA 2024, arXiv:2303.00811.
7. T. de Vos. Minimum Cost Flow in the CONGEST Model. arXiv:2304.01600.
8. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019, arXiv:1912.11491.
9. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs.
   PODC 2025, arXiv:2411.11718.
10. Y. Chen, Z. Tan. Paths and Intersections: Characterization of Quasi-metrics in Directed
    Okamura-Seymour Instances. SODA 2025, arXiv:2410.19246.
11. G. L. Miller, J. Naor. Flow in planar graphs with multiple sources and sinks. SIAM J.
    Comput. 24(5), 1995.
12. R. Hassin. Maximum flow in (s,t) planar networks. Inform. Process. Lett. 13(3), 1981.
13. M. Thorup. Compact oracles for reachability and approximate distances in planar digraphs.
    J. ACM 51(6), 2004.
14. M. Ghaffari, M. Parter. Near-Optimal Distributed DFS in Planar Graphs. DISC 2017.
15. M. Ghaffari, B. Haeupler. Distributed Algorithms for Planar Networks I: Planar Embedding.
    PODC 2016.
16. B. Jauregui, P. Montealegre, I. Rapaport. Deterministic Distributed DFS and Other Problems
    via Cycle Separators in Planar Graphs. PODC 2025, arXiv:2504.21620.
17. Y. Abd-Elhaleem, M. Dory, O. Weimann. A Simple Distributed Deterministic Planar Separator.
    SIROCCO 2026, arXiv:2602.22916.
18. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in
    Undirected Planar Graphs. arXiv:2608.09500, to appear in DISC 2026.
19. M. Parter. Distributed Planar Reachability in Nearly Optimal Time. DISC 2020.

## License

Copyright 2026 Sebastian Senge. The code and the documentation in this repository are licensed
under the Apache License 2.0; see `LICENSE`.
