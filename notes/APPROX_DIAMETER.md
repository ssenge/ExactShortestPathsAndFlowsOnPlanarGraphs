# (1+ε)-approximate eccentricities of unweighted planar networks in Õ(D + 1/ε⁴) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/diameter/approx.py`. No human has checked it. It uses the region bags of `notes/LEMMA15.md`, Section 9, and the notation of `notes/DIAMETER.md`, whose proofs of Fact 0 and of the cut along P_X it reuses. It does not use the Label Hypothesis, nor the pattern bound of [2]. Importance if it survives: solid, since for constant ε it is optimal up to polylogarithmic factors.

The model is CONGEST on a connected, undirected, unweighted planar network with n vertices and hop diameter D, with a known embedding. Õ hides factors polylogarithmic in n. Words have O(log n) bits.

## 1. Result

**Approximate Eccentricity Theorem.** For every ε ∈ (0,1], in Õ(D + 1/ε⁴) rounds every vertex u learns a value Ẽ(u) with ecc(u) ≤ Ẽ(u) ≤ (1+ε)·ecc(u). So a (1+ε)-approximation of the diameter and of the radius are computed in the same bound. Given the embedding, the algorithm is deterministic.

**Additive form.** For any integer ρ ≥ 1, the same proof gives eccentricities with additive error Õ(ρ) in Õ(D + (D/ρ)⁴) rounds. For ρ about D^{3/4} this takes Õ(D) rounds.

**Context.** The bound of [1, Theorem 1.5] for a (1+ε)-approximation of the weighted diameter is Õ(D³) + poly(log(nW)/ε)·D², randomized. For the exact diameter of unweighted networks, the stated bound is Õ(D³) [2], and `notes/DIAMETER.md` claims Õ(D²). To our knowledge there is no better approximate bound for unweighted networks. The term D cannot be removed: take a path with L edges, L ≥ 1/(2ε), and pendant vertices at its far end, and the same with ⌈(1+2ε)L⌉ edges and equally many vertices. A vertex at the near end has the same view for about L rounds, and its eccentricity differs by more than a factor 1+ε.

The idea follows [1, 3, 4]: since the diameter is D, an additive error of εD is allowed, so Õ(1/ε) portals replace Õ(D) hubs. Distance vectors to the portals are rounded, and their number is polynomial by a VC-dimension argument. [1] also counts rounded vectors this way, with finer levels and a different count.

## 2. Parameters and nets

Let r be the root of T and Δ = ecc(r), found by a BFS, so D ≤ 2Δ. Let H be a known upper bound on the height of the tree of bags, H = O(log n), and let

    ρ = ⌊ ε·Δ / (2(2H + 5)) ⌋.

If ρ = 0, then D = Õ(1/ε). In that case run the algorithm below with N_X = L_X, every occurrence with vertex in V(X) a portal, and r = g. All errors vanish, and Lemma 4 gives O(K_Φ⁴) words per face, so Õ(D⁴) = Õ(1/ε⁴) rounds. The exact algorithm of `notes/DIAMETER.md` would take Õ(D²) rounds, but it uses [2]. From now on ρ ≥ 1.

For a non-leaf X, P_X, L_X, the faces, walks, corners and occurrences are as in `notes/DIAMETER.md`, and each q ∈ L_X announces itself over T_X, so every vertex of X knows L_X. Since V(X) ⊆ V(A) for the parent A, (H3) gives that a vertex of V(X) off P_X lies in X°, and its child is X when A is the parent on its chain. Let ℓ_X be the hop metric of P_X. For a leaf X, let T_X be broadcast over itself, in Õ(D) words, let ℓ_X be its hop metric, and let L_X = V(X). In both cases ℓ_X(x,y) ≥ d_G(x,y), since the edges are real. Let M_X be the number of edges of P_X or of T_X, so M_X = Õ(D).

The *net* N_X is the first-fit maximal subset of L_X, in order of identifiers, whose points are pairwise more than ρ apart in ℓ_X. So every x ∈ L_X has a point near(x) ∈ N_X, the first in that order, with ℓ_X(x, near(x)) ≤ ρ. All vertices of X compute it locally.

**Lemma 1.** |N_X| ≤ 1 + 3M_X/ρ, and this is Õ(1/ε).

*Proof.* For ρ = 1 the bound follows from |L_X| ≤ M_X + 1. For ρ ≥ 2, the balls of radius ⌊ρ/2⌋ around the points are disjoint. If there are at least two points, each ball holds at least ⌊ρ/2⌋ ≥ ρ/3 edges, since the graph is connected. ∎

## 3. The vectors τ and single crossing

Let X be a non-leaf. As in Step 3 of `notes/DIAMETER.md`, source detection [5] in W′ from all occurrences with vertex in V(X), to depth 2Δ + K_max, takes Õ(D) rounds. It gives f_v(o) for each v ∈ V(X) off P_X and each such occurrence o on the face Φ_v of v. Let walk(o,o′) be the distance along the walk of Φ_v, and let

    τ_v(o) = min_{o′} f_v(o′) + walk(o′,o)

for all occurrences o of Φ_v. Each vertex computes this locally. There are no further messages, and in particular no table of chords. So τ_v is 1-Lipschitz along the walk, and τ_v(o) ≥ d_G(v, x(o)), since it describes a real walk.

The graph W″_Φ is the part of W′ in Φ, with one more cycle around it: one node ō per occurrence o, edges in both directions between consecutive ō, of length 1, and one arc from o to ō of length 0. It is a directed plane graph in a closed disc with the outer cycle as boundary, and τ_v(o) is the distance from v to ō in it. The depth 2Δ + K_max is enough, since τ_v(o) ≤ D + K_Φ: by Fact 0 a shortest path from v to S_X gives an occurrence at distance at most D.

**Lemma 2 (arcs).** Let u, v lie in Φ, let f = τ_u − τ_v on the occurrences of Φ, and let c be a number. Then {o : f(o) > c} is an arc of the walk, or empty, or everything. The same holds for {o : f(o) < c}.

*Proof.* Otherwise there are positions p₁, p₂, p₃, p₄ in cyclic order with f(p₂), f(p₄) > c ≥ f(p₁), f(p₃). Take shortest paths π₁, π₃ in W″_Φ from u to p̄₁, p̄₃, and σ₂, σ₄ from v to p̄₂, p̄₄. The set π₁ ∪ π₃ is connected and holds p̄₁ and p̄₃, so in the disc it separates p̄₂ from p̄₄, or contains one of them. So σ_j meets π_i at a vertex w, for some j ∈ {2,4} and i ∈ {1,3}. Exchange the parts after w. Both paths are directed towards the boundary, so τ_u(p_j) + τ_v(p_i) ≤ τ_u(p_i) + τ_v(p_j), that is f(p_j) ≤ f(p_i). This contradicts f(p_j) > c ≥ f(p_i). The second claim follows by exchanging u and v. ∎

**Portals.** Start each walk at a canonical corner, say the least by identifiers. Scan the occurrences of Φ with vertex in V(X), in walk order. The first is a portal, and a later one becomes a portal if it is more than ρ steps behind the last portal. So every such occurrence is at most ρ steps after a portal, and there are m_Φ ≤ K_Φ/ρ + 1 portals ô₁, …, ô_m. A face with no such occurrence holds no vertex of X.

**Patterns.** For v in Φ the *offset* is τ_v(ô₁), and g_v(i) = τ_v(ô_i) − τ_v(ô₁). The *rounded pattern* is r_v(i) = ⌊g_v(i)/ρ⌋. Since τ_v is 1-Lipschitz, r_v takes at most Y_Φ = K_Φ/ρ + 2 values.

**Lemma 3 (single crossing).** For u, v in Φ the sequence g_u − g_v, with zeros removed, has at most one change of sign.

*Proof.* Apply Lemma 2 with c = f(ô₁). The positions with g_u − g_v > 0 lie in an arc that does not hold ô₁, and so do those with g_u − g_v < 0. So each is an interval of the linear order ô₂, …, ô_m, and the two intervals are disjoint. ∎

**Lemma 4 (count).** Let I be a set of m′ portals of Φ. The restrictions of the rounded patterns of Φ to I take at most 1 + N + N(N−1)/2 values, with N = m′·Y, where Y ≤ Y_Φ is the number of levels.

*Proof.* Let v correspond to the set A_v = {(i,y) : i ∈ I, g_v(i) ≥ yρ} of grid points, with y over the Y_Φ levels. The restriction of r_v is determined by A_v. This family shatters no three points. Two points with equal i cannot be shattered, since A_v is monotone in y. If i₁ < i₂ < i₃, shattering gives v with the first and the third point but not the second, and w with the second but not the others. Then g_v − g_w is positive, negative, positive at i₁, i₂, i₃, against Lemma 3. So the VC dimension is at most 2, and the Sauer-Shelah lemma gives the bound. ∎

## 4. The algorithm

Depths run one after the other, top down, and bags of one depth in parallel by (H2).

**Estimates h.** For a non-leaf X, v ∈ V(X) and x ∈ L_X, let h^X_v(x) = ℓ_X(v,x) if v ∈ P_X, and otherwise

    h^X_v(x) = min_{o on Φ_v} f_v(o) + ℓ_X(x(o), x).

It is local, it describes a real walk, so h^X_v(x) ≥ d_G(v,x), and it costs nothing beyond f.

**Estimates e.** Invariant: every v ∈ V(X) knows, for each c ∈ N_X, a value e_v(c) with

    d_G(v,c) ≤ e_v(c) ≤ d_G(v,c) + 2ρ·depth(X).

At the root, run a BFS from each point of the net, by source detection, in Õ(D + 1/ε) rounds. Let X have parent A. Run source detection in R_X from N_X to depth 2Δ, in Õ(D + 1/ε) rounds, which gives values b_v(c). Each c ∈ N_X broadcasts its row e_c(c″), c″ ∈ N_A, over T_X, in Õ(1/ε²) words. Then

    e_v(c) = min( b_v(c), min_{c″ ∈ N_A} h^A_v(c″) + e_c(c″) ).

*Proof.* Every value describes a real walk or is at least the distance by the invariant, so the lower bound holds. Let π be a shortest path from v to c. If π avoids P_A, then v is off Q_A, so A is on the chain of v, and by Fact 0, π lies in R_X, with at most D hops. Otherwise let p be its first vertex on P_A. If v ∈ P_A, then p = v. Otherwise Fact 0 gives that the part up to p lies in R_A, so p ∈ L_A, and this part is a path in W′, so it gives f_v(o) ≤ d_G(v,p) for the corner o of its last edge. Let c″ = near(p). Then h^A_v(c″) ≤ d_G(v,p) + ρ, and

    e_c(c″) ≤ d_G(c,c″) + 2ρ·depth(A) ≤ d_G(c,p) + ρ + 2ρ·depth(A).

The sum is at most d_G(v,c) + 2ρ + 2ρ·depth(A). ∎

**Dictionary.** On the portals of each face with m_Φ ≥ 2 fix a segment tree, by halving. Going up level by level, as in Step 4 of `notes/DIAMETER.md`, each vertex of X° off P_X forms for each node I the pair of identifiers of its restrictions to the children of I, and all pairs of one level go up T_X by a filtered upcast, with duplicates removed. Then the root of T_X numbers them and broadcasts them. A leaf of the tree is one rounded value. By Lemma 4 a node with m′ portals holds O((m′Y_Φ)²) values, so the words of one face are Σ_{m′} (m_Φ/m′)·O((m′Y_Φ)²) = O((m_ΦY_Φ)²) = O((K_Φ/ρ)⁴), since K_Φ > ρ here. A face with m_Φ = 1 has one pattern and needs no dictionary.

**Tokens.** For each face and rounded pattern, compute by a convergecast over T_X the largest offset, the child of a vertex that attains it, and the largest offset among vertices in another child. For each c ∈ N_X compute A_X(c) = max_{v ∈ X°} e_v(c). All of it is broadcast over T_X.

**Rounds.** With κ = Σ_Φ K_Φ/ρ ≤ 2M_X/ρ = Õ(1/ε), the number of keys is at most Σ_{K_Φ>ρ} O((K_Φ/ρ)⁴) + Σ_{K_Φ≤ρ} 1 = O(κ⁴) + 2M_X = Õ(1/ε⁴ + D). So each depth costs Õ(D + 1/ε⁴) rounds, and there are O(log n) depths.

## 5. Eccentricities

For a portal ô of a face of X let c(ô) = near(x(ô)). For a token with offset w and rounded pattern r on a face Φ′ let

    val(u, Φ′, r, w) = min_i ( e_u(c(ô_i)) + w + ρ·r(i) ).

For u, and each bag X on its chain, let E_X(u) be the maximum of:
- (a) e_u(c) for c ∈ N_X;
- (b) A_X(near(u)), if X is no leaf and u ∈ L_X;
- (c) if X is no leaf and u is off P_X: val(u, Φ′, r, w) for each face Φ′ and rounded pattern r on it. On the face of u the token must have another child than u, and otherwise it is the token of largest offset.

Let E′(u) = max E_X(u) over the chain, and Ẽ(u) = E′(u) + 2ρ. All of this is local.

**Lemma 5.** ecc(u) − 2ρ ≤ E′(u) ≤ ecc(u) + (3 + 2H)ρ.

*Proof, upper bound.* In (a), e_u(c) ≤ d_G(u,c) + 2ρH. In (b), A_X(near(u)) = e_v(near(u)) for some v, and this is at most d_G(v,u) + ρ + 2ρH. In (c), let the token be attained by v′, so w = τ_{v′}(ô₁) and ρ·r(i) ≤ g_{v′}(i). By the rule on children, u and v′ are in different faces or different children, so by Lemma 1 of `notes/DIAMETER.md` a shortest path π from u to v′ meets P_X. Let b be its last vertex on P_X, so b ∈ L_X by Fact 0. Let o_b be the corner of the last edge of π at b, and let ô be a portal at most ρ steps before o_b, with c′ = c(ô). Then:
- τ_{v′}(ô) ≤ d_G(v′,b) + ρ, and ℓ_X(x(ô), b) ≤ ρ, so d_G(c′,b) ≤ 2ρ;
- e_u(c′) ≤ d_G(u,c′) + 2ρH ≤ d_G(u,b) + 2ρ + 2ρH.

So val ≤ e_u(c′) + τ_{v′}(ô) ≤ d_G(u,v′) + 3ρ + 2ρH.

*Lower bound.* Let v be any vertex, and let X be the last bag on both chains. If X is a leaf, let c = near(v). Then e_u(c) ≥ d_G(u,c) ≥ d_G(u,v) − ρ. If u ∈ L_X, then (b) gives A_X(near(u)) ≥ e_v(near(u)) ≥ d_G(u,v) − ρ. If v ∈ L_X, then (a) with near(v) gives the same. Otherwise both are off P_X in different children. For the rounded pattern r_v, the value with the offset w_v of v is, for each i,

    e_u(c(ô_i)) + w_v + ρ·r_v(i) ≥ d_G(u, c(ô_i)) + τ_v(ô_i) − ρ ≥ d_G(u, x(ô_i)) − ρ + d_G(v, x(ô_i)) − ρ ≥ d_G(u,v) − 2ρ.

The admitted token has an offset at least w_v, even on the face of u, since v has another child, and val grows with the offset. ∎

*Proof of the theorem.* By Lemma 5, ecc(u) ≤ Ẽ(u) ≤ ecc(u) + (5 + 2H)ρ. Further (5 + 2H)ρ ≤ εΔ/2, and ecc(u) ≥ diam/2 ≥ Δ/2. So Ẽ(u) ≤ (1+ε)·ecc(u). The maximum and the minimum of Ẽ over V give the diameter and the radius within the same factor, by one convergecast over T. ∎

## 6. Checks

Results are in `sim/diameter/REPORT_APPROX.md`. `approx.py` builds real region bags for several values of ρ, computes the nets, e, h, τ, tokens and hub maxima as above, and checks the invariant, Lemmas 1, 3 and 4, the bounds of each token, and Lemma 5 against BFS for every vertex. Negative controls in `approx.py ctl` and `approx.py second`.

The constant 3 of Lemma 5 is reached at depth 0, and in the tests the shortfall stays below 2ρ. The theorem needs closing curves that do not cross an edge of G, as Lemma B5 gives them: instances whose closing curves cross an edge of G fail.

Lemma 4 is tight up to a factor of about 40. On a k × k grid with P the boundary cycle and Φ its inner face, with m²/K held near 0.4, the number of rounded patterns is about 0.014·m⁴: for example 34,697 patterns against the bound 1,381,954 at k = 1000, K = 3,996, ρ = 101, m = 40. This comes from a stand-alone script, `sim/diameter/grid_patterns.py`, and the cause is not proved: portals on two adjacent sides seem to give thresholds on x and on y that multiply. On a real forced root bag with k = 40 the rounded patterns saturate at one per interior vertex, and all checks pass.

## 7. Not covered by the checks

- Rounds, messages and who knows what: no CONGEST simulation.
- The proofs of Lemmas B1 and B5, and of the statements (H1) to (H4), except that the simulator exercises them on its instances.
- ρ is a free parameter in the simulator, since on its families the ρ of Section 2 with small ε would be 0. So `approx.py` does not run the ρ of Section 2 or the branch ρ = 0.
- The polylogarithmic exponents, [5] at the source, and the full pipeline above n = 1,600.

## 8. Open

- The exponent 4. Lemma 4 counts grid points by Sauer-Shelah, and uses no more than single crossing. At ρ = 1 it gives K⁴, while [2] gives O(K²). A better exponent cannot come from counting rounded patterns on large D: about 0.014·m⁴ of them occur on grids, see Section 6. Tokens could still be dropped by domination or a packing. Rounding alone cannot do better from pairwise conditions: exact search over lattice paths of m positions, with the single crossing condition only, gives largest families of 9, 25, 61 for m = 3, 4, 5, which is about m⁴/10. A packing may do better. For vectors in {−1,+1}^K with sum 0 and no cyclic alternation, exact search for the largest family with pairwise L∞ distance of prefix sums at least τ gives 17 and 5 for K = 8, τ = 2, 4, and 26 and 6 for K = 10, τ = 2, 4. This fits (K/τ)² + 1, on very small cases only. A proof would allow tokens for a packing of patterns, by a filtered upcast with pruning.
- The (1+ε)-approximation of the sum of distances. An additive error of εD per vertex is not a factor (1+ε) if most vertices are close to u.
- Weighted networks with bounds below [1]. Lemmas 2 to 4 do not use unit lengths, but the first hits f would need exact distances, and the argument for net sizes needs a bound on the weighted length of P_X.

## References

1. J. Li, M. Parter. Planar Diameter via Metric Compression. STOC 2019.
2. V. Fredslund-Hansen, S. Mozes, O. Weimann. A Tight Bound for Facial Distance Patterns in Planar Graphs. arXiv:2608.07187.
3. O. Weimann, R. Yuster. Approximating the Diameter of Planar Graphs in Near Linear Time. ACM Transactions on Algorithms 2016.
4. T. M. Chan, D. Skrepetos. Faster Approximate Diameter and Distance Oracles in Planar Graphs. ESA 2017.
5. C. Lenzen, D. Peleg. Efficient distributed source detection with limited bandwidth. PODC 2013.
