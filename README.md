# Exact Shortest Paths and Flows on Planar Graphs

This repository contains proofs, machine-checked lemmas and numerical checks for exact
single-source shortest paths (SSSP) and exact maximum flow in planar networks in the CONGEST
model. The two main claims are:
- exact directed SSSP in $\tilde O(D)$ rounds (Theorem A), down from $\tilde O(D^2)$;
- exact maximum st-flow in directed planar networks in $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$
  rounds (Theorem C), down from $\tilde O(D^2)$.

Theorem A depends on the distance labels of the recent preprint [1]. One lemma of [1]
(Lemma 14) is false as stated. This repository shows why and gives a repair.

## Status

Please read this before relying on anything here.
- The proofs are written up in `notes/`, not yet as a paper. **No human expert has checked
  them.** Every review so far was done by AI agents: a referee pass and an adversarial pass on
  each layer. AI reviewers can share blind spots with the AI that helped write the proofs.
- **Theorems A, B, C and C′ are conditional on Lemma 14′**, our replacement for the false
  [1, Lemma 14]. Lemma 14′ is proved in `notes/LEMMA15.md` §3. A referee pass found it correct
  given its assumptions and raised one serious point, which is fixed. An adversarial pass on
  the earlier draft broke nothing and found only the referee's points again. An adversarial
  pass on the fixed text has not been run yet.
- All results hold with high probability. They would be deterministic if the bounded-diameter
  decomposition (BDD) of [8] could be built deterministically, which is open.
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

Two open questions are stated at the end of [9]. The first asks for better primal SSSP, which
is called "the bottleneck to overcome in order to obtain better distributed planar
algorithms". The second asks to "first improve the $\tilde O(D^2)$ bound of the (easier)
directed SSSP problem (even with non-negative weights)".

## Results

| Result | Rounds | Previous | Rating |
|---|---|---|---|
| Theorem A: exact SSSP, directed, $w\ge0$ | $\tilde O(D)$ | $\tilde O(D^2)$ [8] | modest to solid |
| Theorem B: exact SSSP with negative weights, or a negative cycle | $D\cdot n^{o(1)}$ | $(\sqrt n+D)\cdot n^{o(1)}$ on general graphs [6] | modest |
| Theorem C: exact maximum st-flow, directed | $\min\lbrace\tilde O(D^2),\ D\cdot n^{o(1)}\rbrace$ | $\tilde O(D^2)$ [9] | significant |
| Theorem C′: the same with $s$, $t$ on a common face | $\tilde O(D)$ | approximate and undirected only [9] | modest |
| Lemma V: distances from a virtual source, and a fix of the query of [1] | $\tilde O(D/\varepsilon)$ | | minor |
| Lemma D: the face-disjoint graph of [9], weighted, realizes dual distances | | | minor |
| [1, Lemma 14] is false | | | modest |
| Lemmas 14′, 15′, 16′: the repair of [1, Lemmas 14 to 16] | | | minor |

All four theorems are conditional on Lemma 14′ (see [Status](#status)). The ratings in short:
- **Theorem A** closes the planar exact-SSSP gap up to polylogarithmic factors and answers
  the second question of [9]. The proof is short, though: the reduction of [3], the labels of
  [1], and Lemma V. Since [3, §3.1] already says its boosting works in any model that can run
  its oracle, the theorem is close to folklore once the labels of [1] are available.
- **Theorem B** is a white-box substitution into [6].
- **Theorem C** brings the main theorem of [9] from $\tilde O(D^2)$ to $D\cdot n^{o(1)}$, close
  to the $\Omega(D)$ lower bound. The new term wins once $D$ exceeds $(\log n)^{O(\sqrt{\log n})}$.
  The proof is entirely a composition of known pieces.
- **Theorem C′** is the proof of [9, Thm 1.3] with an exact oracle plugged in.
- **The finding about [1, Lemma 14]** is a correctness gap in the main CONGEST result of an
  unrefereed preprint. The repair changes no bound.

### Theorem A (exact SSSP)

**Theorem A.** Let $G$ be a planar digraph with nonnegative integer weights in
$\lbrace 0,\dots,n^{O(1)}\rbrace$, hop diameter $D$ and source $s$. A CONGEST algorithm computes
exact distances from $s$ and a shortest-path tree in $\tilde O(D)$ rounds with high probability.

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
$\tilde O(D)$ rounds with high probability, for directed networks. This is the method of [12]:
add a chord between $s$ and $t$ inside the face and compute one dual SSSP with nonnegative
lengths. [9, Thm 1.3] gives a $(1-o(1))$-approximation for undirected networks in
$D\cdot n^{o(1)}$ rounds.

## What is assumed

Beyond the results cited in the proofs, these enter as black boxes:
- **(G1) The decomposition** of [1, Lemma 9], as built in [8, Sec. 4.2]. We use the shape of
  its child bags as we read it off [8], and spanning trees of diameter $O(D\log n)$ per bag.
  [1] states height $O(D)$, which [8] does not give; the difference costs one log factor.
- **(G3) Realization**, [10, Thm 1].
- **(G4)** Distances in a graph drawn in a disk satisfy the Monge condition in boundary order.
  This is standard, and the notes give the proof.
- **(G5) Distance oracles** for planar digraphs [13], as used in [1, Lemma 11].
- **(G6) Face identifiers** in $\tilde O(D)$ rounds [9, Lemma 5.11].

## Machine-checked proofs (`lean/`)

Lean 4 (`leanprover/lean4:v4.36.0-rc1`) with Mathlib; the exact Mathlib revision is pinned in
`lean/lake-manifest.json`. All theorems depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry`. In a fresh clone, run
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
  of Lemma 16′ in both directions. The separation property of the child bags enters as a
  closure hypothesis on arcs.
- `lean/SsspFlow/Boost.lean`, theorem `SsspFlow.Boost.Run.exact`: the discretized boosting of
  [3] with base $\ell_i+\eta$. Lengths stay nonnegative (`Run.len_nonneg`), every vertex
  contracts by a factor $1-1/\alpha$ up to an additive $(n-1)\eta$, and the final rounding is
  exact once the stated bounds hold. `c1_negative` is the one-arc instance where base $\ell_i$
  gives $-\eta$.

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
- `sim/attack/`: the counterexamples to [1, Lemma 14], and checks of the analytic layer:
  gluing (`r1_glue.py`), rounding (`r6_round.py`), the error recursion (`l16.py`), the squaring
  in [1, Thm 2] (`s1_square.py`), and the first adversarial runs on Lemma V and Lemma D
  (`lemmaV.py`, `lemmaD_flow.py`). `rot.py` is a small rotation-system library used by the
  others.
- `sim/ref/monge.py`: an instance that satisfies the Monge constraints of [1] for one linear
  reading of the order but not for the circular one, which is why the notes impose them in all
  rotations.

## Notes (`notes/`)

- `notes/NOTES.md`: the state of the art, Theorems A, B, C and C′, Lemmas V and D, the ratings,
  and the review history.
- `notes/LEMMA15.md`: the gaps in [1, Lemmas 14 to 16] and their repair, with Lemma 14′ (§3),
  the analytic layer (§4 to §7), and what is settled (§8).

These are working notes. References such as "lty 1762" or "adpw 2166" point to line numbers in
plain-text extractions of [1] (arXiv v2) and [9].

## Open questions

- Directed planar global minimum cut is at $\tilde O(D^2)$ [9, Thm 1.5]. It needs the shortest
  cycle of simple darts in the dual. $\hat G$ has cycles of weight 0, so the girth of
  $\hat G$ does not give it.
- Weighted girth of planar digraphs, also at $\tilde O(D^2)$.
- Can the $n^{o(1)}$ in Theorem C be removed? That needs a reduction for negative weights with
  polylogarithmic overhead.
- Is there a deterministic decomposition with the properties of [1, Lemma 9]? It would make
  all four theorems deterministic.
- Can the realization step run in polynomial local time?

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

## License

Copyright 2026 Sebastian Senge. The code and the documentation in this repository are licensed
under the Apache License 2.0; see `LICENSE`.
