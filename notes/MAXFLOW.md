# Exact maximum flow, with the flow on every edge, in Õ(D) rounds

**Status.** Claim, written 2 Nov 2026. Proofs below, simulation in `sim/maxflow/`. On parallel arcs of one direction a number of iterations chosen from nU gives an infeasible flow, so τ is chosen from mU, see Section 3. No human
has checked it. It rests on the Label Hypothesis of [1] and on one extension, (L3). (L3) does not follow from the Hypothesis as a statement; Section 5 obtains it from the construction in `notes/LEMMA15.md`, so the theorem rests on that construction and on its black boxes (G3), (G5), (G6) and the embedding, with local computation that is not polynomial. Importance if it survives: significant.

**A route without (L3).** `notes/NEGATIVE.md` reaches the same bound, randomized, from the Label Hypothesis alone, by a polylogarithmic reduction for negative weights. It does not need this note, and it is much simpler. This note stays of interest as the deterministic route relative to the labels, and for the method.

**Comparison.** The best exact bounds were Õ(D²) [2], which is randomized and unconditional, and D·n^{o(1)} [1], which is randomized and conditional. So this claim does not dominate [2] unconditionally. [3] calls finding the flow assignment in Õ(D) rounds an open question, in the context of its unconditional undirected (1−o(1))-approximation. This note answers it conditionally, and for exact directed flow.

The model is CONGEST on a connected planar network with n vertices and hop diameter D, with a known embedding. Õ hides factors
polylogarithmic in n. Statement names (Exact SSSP Theorem, Virtual Source Lemma, Dual Distance Lemma, Dual SSSP Corollary, Label Hypothesis) are
those of [1].

## 1. Result

**Hypothesis (L3), prescribed root cycle.** In the setting of the Label Hypothesis, let the network also have a spanning tree T of height O(D)
and a simple cycle S that bounds a face and consists of a path of T and one further edge. Then a hierarchy with (L1) and (L2) can be computed in the same number of
rounds, such that one vertex, the root centre, also knows, for all a, b in S, a value δ(a,b) with dist(a,b) ≤ δ(a,b) ≤ (1+ε)·dist(a,b).

**Flow Theorem.** Let G be a directed planar network with terminals s, t and integer capacities in {0,…,U}, U = n^{O(1)}. Given the Label
Hypothesis and (L3), every vertex learns the value of a maximum st-flow, and the integer flow of a maximum st-flow on each of its edges, in Õ(D)
rounds. The algorithm is deterministic relative to the labels. The cases n = 2 and s = t are trivial, so below n ≥ 3 and s ≠ t.

A minimum st-cut follows from reachability in the residual graph, by the Exact SSSP Theorem. A path gives Ω(D), so the bound is optimal up to
polylogarithmic factors. Only a fixed ε = 1/12 is needed from the labels.

**Idea.** Exact potentials on the at most 2D faces next to one BFS path R decide everything, but their distance matrix has D² entries. A
(1+ε)-approximate matrix fits in Õ(D) words. It gives a flow whose value is a constant fraction of the maximum and which is exactly feasible on every
edge. Its residual network is again a planar network with integer capacities, so the step repeats, and O(log nU) steps get close enough for one
last exact SSSP to finish.

## 2. One step

Notation. A flow is given on darts: f(rev d) = −f(d), and f is feasible for capacities C if f(d) ≤ C(d). Faces are the nodes of the dual, and a dart
d gives the dual arc from rgt(d) to lft(d). Let R be a path from s to t in a BFS tree of G rooted at s, and let σ(d) = 1 on the darts of R, −1 on their
reverses, and 0 otherwise.

As in [5], for face potentials ψ the function ψ(lft d) − ψ(rgt d) + σ(d)β is an st-flow of value β, and every st-flow of value β has this form. It
is feasible for C if and only if ψ(lft d) − ψ(rgt d) ≤ C(d) − σ(d)β for every dart. So a flow of value β exists if and only if the dual with lengths
C − σβ has no negative cycle.

Let Γ be the dual without the arcs of darts with σ ≠ 0. Removing a set of dual edges that contains no primal cycle leaves the dual connected, and every arc of Γ
has its reverse, so Γ is strongly connected. For C ≥ 0 let d_C be the distance in Γ. Let P be a set of nodes, each carrying a face, that contains
rgt(d) and lft(d) for all d with σ(d) ≠ 0. Section 4 takes corner nodes for P; two nodes of one face have d_C = 0 in both directions.

Fix ε = 1/12 and K = 9, so that K ≥ (1+ε)(1+3ε)/(2ε) = 8.125. *Portal bounds* for C are integers b on P × P with

    (B)    K·d_C(u,v)/(1+3ε) ≤ b(u,v) ≤ K·d_C(u,v).

*System(J)*, for an integer J, has integer unknowns ψ on P, where for a dart d with σ(d) ≠ 0 we read ψ(rgt d) at corner(d) and ψ(lft d) at corner(rev d), and the constraints

    ψ(v) − ψ(u) ≤ b(u,v)                         for all u, v in P,
    ψ(lft d) − ψ(rgt d) ≤ K·C(d) − σ(d)·J         for all d with σ(d) ≠ 0.

**Step Lemma.** Let C ≥ 0 be integer capacities with maximum flow value λ, let b satisfy (B), let J be the largest integer such that System(J) is
solvable, and let ψ be a solution. Let

    ϕ(x) = min over p in P of ( ψ(p) + K·d_C(p,x) )    for every face x,
    g(d) = ϕ(lft d) − ϕ(rgt d) + σ(d)·J.

Then:
1. g is an integer st-flow of value J with g ≤ K·C, and ϕ = ψ on P;
2. Kλ/(1+3ε) − 1 < J ≤ Kλ;
3. C′ = K·C − g is a nonnegative integer capacity function with maximum flow value Kλ − J ≤ Kλ/5 + 1, and C′(d) + C′(rev d) = K·(C(d) + C(rev d)).

*Proof.* (1) By (B), ψ(p) ≤ ψ(q) + b(q,p) ≤ ψ(q) + K·d_C(q,p), so ϕ = ψ on P. For d with σ(d) = 0 the arc lies in Γ, so ϕ(lft d) ≤ ϕ(rgt d) + K·C(d).
For σ(d) ≠ 0 both faces are in P, and the second family of constraints applies. So g ≤ K·C. The flow form gives value J.

(2) The upper bound is (1), since K·C has maximum flow value Kλ. For the lower bound let ψ\* be potentials of a maximum flow for C, so
ψ\*(lft d) − ψ\*(rgt d) ≤ C(d) − σ(d)λ. Put κ = K/(1+3ε) ≤ K. Summing along a path in Γ, where σ = 0, gives ψ\*(v) − ψ\*(u) ≤ d_C(u,v), hence
κψ\*(v) − κψ\*(u) ≤ κ·d_C(u,v) ≤ b(u,v). On darts with σ ≠ 0, κ(ψ\*(lft d) − ψ\*(rgt d)) ≤ κC(d) − σ(d)κλ ≤ K·C(d) − σ(d)κλ, as C ≥ 0. Now let J′ = ⌊κλ⌋, and if λ > 0 put θ = J′/λ ≤ κ.
The same two lines hold with θ in place of κ, using d_C ≥ 0 and C ≥ 0, so θψ\* is a real solution of System(J′). For λ = 0, ψ = 0 solves System(0), since b ≥ 0 and C ≥ 0. The data are integers, and
ψ(v) ≤ ψ(u) + w with w an integer gives ⌊ψ(v)⌋ ≤ ⌊ψ(u)⌋ + w, so floors give an integer solution. Hence J ≥ J′ > κλ − 1.

(3) C′ ≥ 0 by (1), and it is integer. It is the residual network of g in K·C, so its maximum flow value is Kλ − J. By (2) this is below
Kλ(1 − 1/(1+3ε)) + 1 = Kλ/5 + 1. The last identity holds because g is antisymmetric. ∎

Solvability of System(J) is monotone in J on J ≥ 0: for 0 ≤ J₁ < J₂, the convex combination of a solution for J₂ and the solution 0 for J = 0 solves System(J₁), and floors make it integer. Any solvable J is at most Kλ. So one vertex that knows b and C on R finds J and ψ by local binary
search, with ceiling J ≤ K·(max flow value) ≤ K^{i+1}·mU in pass i, and Bellman-Ford. We normalize min ψ = 0.

## 3. From approximate to exact

Set C_0 = c, β_0 = 0, Φ_0 = 0, and iterate the Step Lemma with J_i and ϕ_i:

    C_{i+1} = K·C_i − g_i,    β_{i+1} = K·β_i + J_i,    Φ_{i+1} = K·Φ_i + ϕ_i.

We write τ for the number of iterations. By induction,

    (I)    C_i(d) = K^i·c(d) − ( Φ_i(lft d) − Φ_i(rgt d) ) − σ(d)·β_i,

and the maximum flow value of C_i is p_i := K^i·λ − β_i ≥ 0, where λ is the value for c. Part 2 of the Step Lemma gives 5J_i ≥ 36p_i − 4, so 5p_{i+1} ≤ 9p_i + 4, and by induction

    5^τ·p_τ + 5^τ ≤ 9^τ·(λ + 1),    so    p_τ / K^τ < (λ + 1) / 5^τ.

Let F be the number of faces plus 1, let m be the number of arcs, parallel ones included, and let τ be the least integer with 5^τ ≥ F·(mU + 1). Then τ = O(log nU) for m = n^{O(1)}, and p·F < K^τ for p = p_τ, since λ ≤ mU. The bound λ ≤ nU would fail on parallel arcs.

**Exactness Lemma.** With Φ = Φ_τ, β = β_τ:
1. λ = ⌈β/K^τ⌉, and p = K^τ·λ − β;
2. r(d) := K^τ·(c(d) − σ(d)λ) + Φ(rgt d) − Φ(lft d) + p is a nonnegative integer for every dart;
3. for a fixed face f_0 and with dist_r the distance in the full dual, π(x) := ⌊( dist_r(f_0,x) − Φ(f_0) + Φ(x) ) / K^τ⌋ is the distance from f_0 in the dual with lengths ℓ = c − σλ;
4. f(d) := π(lft d) − π(rgt d) + σ(d)λ is a maximum st-flow, feasible for c and integer.

*Proof.* (1) 0 ≤ p < K^τ/F. (2) By (I), r(d) = C_τ(d) + (1 − σ(d))·p ≥ 0. (3) For a dual path Q from f_0 to x, the potentials telescope:

    r(Q) − Φ(f_0) + Φ(x) = K^τ·ℓ(Q) + p·|Q|.

Since r ≥ 0, dist_r is attained by a simple path. Since λ is a feasible value, ℓ has no negative cycle, so dist_ℓ is also attained by a simple path. A simple path has |Q| < F, so p·|Q|/K^τ < 1. Divide by K^τ. Every simple
path gives at least ℓ(Q) ≥ dist_ℓ(f_0,x), and a shortest one gives less than dist_ℓ(f_0,x) + 1. So the floor is dist_ℓ(f_0,x).
(4) The triangle inequality for ℓ gives f ≤ c, and the flow form gives value λ. ∎

Numbers stay polynomial: K^τ = (nU)^{O(1)}, part 3 of the Step Lemma gives C_i(d) ≤ K^i·2U, and with min ψ = 0 we get ψ ≤ K·F·K^i·2U, ϕ_i ≤ 2K·F·K^i·2U and Φ_τ ≤ τ·K^τ·4FU.

**Parallel arcs and the choice of τ.** The bound λ ≤ nU fails on parallel arcs of one direction, and a τ chosen from it gives a wrong result. With 10 parallel s-a arcs and 10 parallel a-t arcs, all of capacity 1, λ = 10 exceeds nU = 3. The value still comes out right, but the potentials are wrong and f is infeasible for 8 of 19 choices of f_0. This is why τ is defined with mU. Antiparallel pairs do not cause it, since the capacity out of s is then at most (n − 1)U.

The number τ cannot be lowered in general: on K_{2,124} with U = 124 the ratio p·F/K^τ reaches 0.976 with τ = 9, and τ − 1 gives wrong potentials and an infeasible f on all 124 faces.

## 4. The network N

N is the face-disjoint graph Ĝ of [2], as described in [1], with two changes. Write corner(d) for the corner node at the tail of d, in the face rgt(d).
So the E_R edge of a dart d joins corner(d) to corner(next d), where next d follows d on the boundary walk of rgt(d).

- The E_C edges of the edges of R are removed.
- The star centre of an interior vertex v of R is split in two. The edges of R at v cut the rotation of v into two wedges, the *banks*, and each copy keeps
  the star edges of one bank. A star centre with a single corner is omitted.

Lengths ℓ_C on N are those of the Dual Distance Lemma for capacities C ≥ 0: 0 on E_R, C(d) from the corner in rgt(d) to the corner in lft(d) on E_C, and M on E_S,
with M > |V(N)|·max C. As in [1], loops are dropped (a degree-1 vertex gives an E_C loop) and of parallel edges the lightest arc in each direction is kept (a degree-2 vertex gives parallel E_C edges). This changes no distance, and S is untouched, since it uses only spokes and E_R edges. Scaled lengths are 𝓛 = 2|V(N)|·K·ℓ_C + 1, which are integers in [1, poly(n)], with arcs in both directions on every edge.

**Lemma N.** Let G have at least 3 vertices.
1. N is planar, with a rotation that every host derives from its own rotation and the knowledge of R. An r-round algorithm on N runs in 2r rounds on G.
2. N has hop diameter at most 6D + 2.
3. The slit along R is a face of N, bounded by a simple cycle S of at most 6D + 2 nodes, which contains corner(d) for every d with σ(d) ≠ 0.
4. T := S minus one edge, plus a BFS forest of N from S, is a spanning tree of height O(D) that contains a path of S with all its nodes, computed in O(D) rounds.
5. For corner nodes a, b of faces x, y, the distance under ℓ_C is d_C(x,y).
6. If dist_𝓛(u,v) ≤ δ(u,v) ≤ (1+ε)·dist_𝓛(u,v), then b(u,v) := ⌊δ(u,v) / ((1+ε)·2|V(N)|)⌋ satisfies (B).

*Proof.* (1) In the drawing of Ĝ, the curve of an edge of G runs between its two E_R edges and is crossed only by its own E_C edge. So the curve of R from s to t passes only through the
star centres of its vertices, once the E_C edges of R are gone. Cutting the plane along it splits exactly the interior centres, and gives a plane drawing. Hosts stay the same, and N has no E_R or E_C edge that Ĝ does not have, so the
simulation of [2] applies.

(2) Let T_G be the BFS tree of G rooted at s that contains R. For a vertex v, follow its tree path to s, with three hops per edge of G: centre, corner, E_R edge, corner, centre. A non-R edge at a vertex of R arrives on one bank,
and then the path continues along R on that bank, where E_R edges and star copies exist. A path that meets an omitted star centre stays on the single corner. So every node is within 3D + 1 hops of the centre of s, or of its single corner when the centre is omitted.

(3) Walking around the slit: from corner(d_1) along the E_R edge of d_1 to corner(next d_1), through the star copy of the bank (or nothing, when corner(next d_1) = corner(d_2)) to corner(d_2), and so on to t, then back along the other bank
through the corners of the reverse darts. Corners of the two banks are distinct, and a corner occurs twice only as the single corner of s or of t, or of a bank, and is then taken once.

(4) S minus one edge is a path that contains all nodes of S. By (2) each node is within O(D) hops of S.

(5) The Dual Distance Lemma uses only that the E_R edges of a face connect its corners with length 0 and that a path through a star centre has length greater than M. Its graph here is Γ, since exactly the E_C edges of R are gone.

(6) Let d = d_C. A path Q has 𝓛(Q) = 2|V(N)|K·ℓ_C(Q) + |Q|, so 2|V(N)|K·d ≤ dist_𝓛 < 2|V(N)|K·d + |V(N)|. Then δ/(1+ε) ≤ dist_𝓛 gives b ≤ ⌊Kd + 1/2⌋ = Kd. From δ ≥ dist_𝓛, b ≥ ⌊Kd/(1+ε)⌋. If d = 0
this gives b = 0. If d ≥ 1, then b > Kd/(1+ε) − 1 ≥ d·(K/(1+ε) − 1) ≥ Kd/(1+3ε), the last step by K ≥ (1+ε)(1+3ε)/(2ε). ∎

## 5. Where (L3) comes from

The construction of `notes/LEMMA15.md` in its region form (§9), which builds on the labels of [4], already gives the conclusion of (L3) for the root separator it chooses: by Lemma 15′ the root holds a plane digraph H with
dist ≤ dist_H ≤ (1+ε′)^{3h}·dist on ∂S⁺_root = S_root and its (G5) oracle labels, Õ(D/ε′) words, and by Lemma 16′ these labels go to every vertex of the root. What (L3) adds is that S_root is prescribed. We take S_root := S, T as given,
and apply Lemma B5 only below the root. We went through what this touches:

- **Balance.** The balance of Lemma B5 is used only for the height (§9.5). The prescribed cycle may be arbitrarily unbalanced; the height grows by 1, since all later separators come from Lemma B5.
- **Tree.** T need not be a BFS tree. The proof of Lemma B1(e) uses only that T_X ⊇ T ∩ R_X and that a component of T ∩ R_X has diameter at most twice the height of T.
- **Children.** Lemma B1(a) to (d) hold by construction for any simple closed curve. Lemmas B2, B3 and B4 use only that S_X is a path q_X of T_X plus a closing edge. When S bounds a face, as here, the inside part is S with its inside sides, a leaf, and the
  outside child has all vertices and one hole.
- **Tiles.** §3 uses of S_X only that q_X has an edge and the rules for L_X, Q_X, P_X. Γ_1 is connected, since S_root is a cycle whose vertices all lie on q_X.
- **Knowledge.** Every vertex of R broadcasts its degree and the rotation indices of its two edges of R, O(1) words each, so every vertex knows S in O(D) rounds. Rotations in full would not fit: a rim vertex of a wheel cannot learn the rotation of the hub. Since S bounds a face, each vertex knows its side locally: the inside part is S itself.

**Root step.** For facial S, these are the changes to `notes/LEMMA15.md`:
- §9.1 and the proof of Lemma B1(e): BFS is used only for the height of T.
- §9.2: the root separator is prescribed, and the root has no z_s.
- §9.5, Height: the bound (2/3)|X| + |S_X| fails at the root. This costs one extra level, and ε′ is fixed from the bound H + 1.
- §9.6, Bag knowledge: the sides at the root are local, as above, not from Lemma B5.
- §9.9: the δ conclusion comes from Lemma 15′ at the root, which holds H_root at the centre.
- If N has fewer vertices than the leaf threshold, the root is a leaf, and N is gathered at one vertex in Õ(D) rounds.

No other use of balance, of the BFS property, of a nonempty inside, of progress in vertex count, or of the output of Lemma B5 was found, and Lemmas B1 to B4, Claims 1 to 7 and Lemma 15′ go through with the inside part a leaf on S and the outside child holding all vertices and one hole. This is an audit, not a new proof of §3 to §9. `sim/maxflow/forced.py` runs part of the check suite of `sim/s9` on it, see Section 7.

## 6. The algorithm

1. Compute R and T_G in O(D) rounds, broadcast R, build N, S and T. One aggregation in O(D) rounds gives n, m, U, F and a common M.
2. For i = 0, …, τ−1:
   - Run the labels of (L3) on N with lengths 𝓛 for C_i and ε = 1/12. The root centre now knows δ on S, and hence b.
   - The vertices of R send C_i on R to the root centre, which computes J_i and ψ with min ψ = 0, and broadcasts them, Õ(D) words.
   - Run Algorithm Exact of [1], in its stated form with offsets on a set, on N with lengths ℓ_{K·C_i} and offsets ψ at the corners of S. By Lemma N(5) this gives ϕ_i at every corner. A path through a star centre is never minimal: from a start p′ it has length at least ψ(p′) + 2M, and the path from p′ that avoids star centres is shorter than ψ(p′) + M.
   - Every vertex updates C and Φ on its darts locally: the tail of a dart holds the corners of both its faces.
3. Compute λ and p, take f_0 to be a face of a corner on S, so that every vertex knows Φ(f_0) from the values ψ of all passes, and run the Dual SSSP Corollary (a) with lengths r. Every vertex computes π and f on its darts locally.

**Rounds.** Step 1 takes O(D). Each pass of step 2 takes Õ(D), by (L3), Lemma N and the Exact SSSP Theorem, with hop diameter O(D) and lengths of polynomial size. Step 3 takes Õ(D). With τ = O(log n) passes, the total is Õ(D). Everything else is local or one more broadcast, and no step uses randomness outside the labels. ∎

## 7. Checks

Results are in `sim/maxflow/REPORT.md`: 359,477 instances and about 2.2 million iterations with no failure, all controls fired. The algebra of Sections 2 and 3 is in `lean/SsspFlow/FlowScaling.lean`, without `sorry`: the fill, the bound on the residual, the invariant, nonnegative reduced costs, the floor argument and feasibility of the result. Not in Lean: that J is largest and J ≤ Kλ, monotonicity of solvability, Lemma N(6), the choice of τ, part 1 of the Exactness Lemma, flow conservation, and the residual value identity, which enters as a hypothesis. Planarity, the portal metric and rounds are not in Lean either.

`mf.py` runs Sections 2 and 3 on Γ with portal distances perturbed within [d, (1+ε)d] by four fixed noise modes, not by an optimized worst case, and compares against an independent Dinic. `forced.py` builds N for flow instances, checks parts of Lemma N, and runs the construction of `notes/LEMMA15.md` with the prescribed root cycle. Below the root it uses fundamental cycles, not Lemma B5, and bags with no cycle in the tries are left as leaves. Neither script combines N, δ and the Step Lemma.

Several bounds are close to tight. The equality 5J = 36p − 4 occurs in the Step Lemma, and b = K·d occurs in (B). A tree with triangles at the tips gives hop(N) = 6D − 2 and |S| = 6D, against 6D + 2 in Lemma N. A random choice of z_s breaks the hypothesis of Lemma B1(e) and exceeds the c(X) formula, with no wrong value seen.

## 8. Not covered by the checks

Rounds, messages and knowledge are not simulated. The black boxes of `notes/LEMMA15.md` (G3), (G5), (G6), the given embedding, [2, App. A] and the reduction inside Exact are taken as stated. Claims 1 to 7, the R lemmas and Lemmas B1 to B5 of `notes/LEMMA15.md` are read for root-specific uses and not proved again here. A cycle S that does not bound a face is not treated. The oracle in `mf.py` is a perturbation, not (G5). The instances of `mf.py` are simple networks, and it takes the number of iterations from nU, which suffices there, so the parallel arcs of Section 3 are not run. The emulators in `forced.py` are perturbed pieces and wheels, as in `sim/s9`, not realizations by (G3). Lemma B5 below a forced root and real (G3), (G5) labels are not run. Local computation is not polynomial, as for the Label
Hypothesis.

## References

1. S. Senge. Exact shortest paths and flows on planar graphs. 2026. See the README of this repository.
2. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
3. Y. Abd-Elhaleem, M. Dory, O. Weimann. Õptimal Distributed Maximum Flow Approximation in Undirected Planar Graphs. DISC 2026 (shortened version), arXiv:2608.09500.
4. H. Le, H. Tierno, S. Yang. Planar Embedding of Okamura-Seymour Quasimetrics in Polynomial Time with an Application to Distributed SSSP. arXiv:2606.31192.
5. G. L. Miller, J. Naor. Flow in planar graphs with multiple sources and sinks. SIAM J. Comput. 24(5), 1995.
