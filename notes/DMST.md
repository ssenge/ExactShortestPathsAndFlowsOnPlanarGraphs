# Minimum arborescences of planar digraphs in Õ(D) rounds

**Status.** Claim, written 3 Nov 2026. Proofs below, simulation in `sim/dmst/`, the arithmetic in `lean/SsspFlow/Arborescence.lean`. Referee and adversary not yet run. No human has checked it. It rests on the Exact SSSP Theorem and the Label Hypothesis of [1]. Importance: modest. It is a first bound on planar networks for a classical problem, and the plan is that of [2], with the oracle of [1].

The model is CONGEST on a connected planar network G with n vertices and hop diameter D, with a known embedding. Õ hides factors polylogarithmic in n. A *digraph on G* has its arcs on edges of G.

## 1. Results

**Theorem 1 (minimum arborescence).** Let H be a digraph on G with integer weights of polynomial size, possibly negative, and let r be a vertex. Given the Label Hypothesis, in Õ(D) rounds every vertex v ≠ r reached from r learns its in-arc in a minimum-weight arborescence of the set reached from r, with root r, and all vertices learn its weight. The algorithm makes at most log₂ n + 1 calls of the oracle (O) below, and Õ(1) steps of (M). It adds no randomness beyond the labels and the steps of (M).

**Corollary 2 (maximum branching).** In the same bound every vertex learns its in-arc in a maximum-weight branching of H, or that it is a root of the branching.

A path gives Ω(D). If the weights are symmetric, this is the minimum spanning tree, which takes Õ(D) rounds on planar networks by low-congestion shortcuts [3].

**Context.** [2] solves this problem on general networks by Õ(1) calls of a black box for SSSP, with a bound for bidirectional links of Õ(min(√(nD), √n·D^{1/4} + n^{3/5} + D)) at the time. So Theorem 1 follows the plan of [2], and web searches on 3 Nov 2026 found no earlier bound for planar networks, which is not proof that none exists. Three things differ from [2]:

- [2] finds a vertex of each cycle by centers and a center graph, at a cost of about √n. Here a spanning forest gives it in Õ(D), since the one arc that a spanning tree of a component leaves out lies on the cycle.
- [2] runs SSSP in disjoint components through a network with shadow vertices, which is not planar. The oracle of [1] takes offsets and removed arcs, so one call does it with no extra vertices.
- Section 3 has a short and complete proof of one contraction. We read the conference version of [2], whose proofs of correctness are in a full version that we did not read, and which decomposes a step into steps of the algorithm of Edmonds. Section 3 does not need that decomposition.

We did not check whether the unconditional Õ(D²) SSSP of [4] takes offsets and removed arcs in one call. If it does, the same algorithm has that bound unconditionally. Approximation is treated in [5].

## 2. Tools

**(O), the oracle.** As in `notes/NEGATIVE.md`, Section 2. Given nonnegative integer weights of polynomial size on arcs on G, and offsets on a set S, every vertex learns its least value of offset plus distance from S, in Õ(D) rounds. This is the algorithm Exact of [1, Algorithm 1]. An arc is removed by a weight above all that matters. The reversed digraph is a digraph on G as well. With positive weights, each vertex then takes a tight in-arc, which gives a shortest-path forest after one round.

**(M), minor aggregation.** A step of the Distributed Minor-Aggregation Model takes Õ(D) rounds on planar networks [4, Cor. 4.6, Lemma 4.8]. It covers aggregates over connected parts, a spanning forest of a given set of arcs by Borůvka in O(log n) steps, and subtree sums in a rooted forest, as (T2) in `notes/DIRECTED.md` of the planar matching repository.

## 3. One contraction

A *state* is a partition of the vertices into connected sets, the *super-vertices*, with {r} among them, and a multigraph R on the super-vertices, whose arcs are arcs of H between different super-vertices, with weights w ≥ 0. It also has one chosen arc of weight 0 into each super-vertex other than {r}. We call these the *chosen arcs*. Every super-vertex is reached from {r} in R. An *arborescence of R* has one in-arc for each super-vertex other than {r}, and all are reached from {r}.

A weak component of the chosen arcs is *active* if it does not hold {r}. With k super-vertices it has k chosen arcs, so it holds exactly one cycle, and every super-vertex in it is reached along chosen arcs from the cycle. The component of {r} is a tree.

Fix an active component K and a super-vertex c on its cycle. Let d(S) be the distance from S to c in the graph R[K], with d(S) = ∞ if there is no path. So d = 0 on the cycle. Let

β = min { w(u, v) + d(v) : (u, v) an arc of R with u outside K and v in K }.

β is finite: a path from {r} to c enters K a last time. Let A = {S in K : d(S) ≤ β}. The *contraction* merges A into one super-vertex. For each arc (x, y) with y in A and x outside A, the new weight is w′(x, y) = w(x, y) + d(y) − β. Arcs inside A vanish, and all other arcs keep their weights. The new chosen arc of A is an arc that attains β. All other super-vertices keep their chosen arcs.

**Lemma 1.** (a) 0 ≤ w′ ≤ w, and the new chosen arc has weight 0. (b) A shortest path from S in A to c lies in A, the cycle lies in A, and the chosen arc of a member of A has its tail in A. So A is connected, and the result is a state.

*Proof.* (a) Since y is in A, d(y) ≤ β, which gives w′ ≤ w. If x is outside K, then β ≤ w + d(y) by its definition. If x is in K but not in A, then β < d(x) ≤ w + d(y). (b) Distances do not grow along a shortest path, and β ≥ 0 holds for the cycle. If (p, S) is the chosen arc of S in A, then d(p) ≤ 0 + d(S) ≤ β, and p is in K. ∎

**Lemma 2 (unpacking).** Let T′ be an arborescence after the contraction, with (x, y) the in-arc of A, and let S_y be the member of A that holds y. Let π be a shortest path from S_y to c in R[K]. Let T agree with T′ outside A, let S_y get the in-arc (x, y), let each other member of A on π get its arc of π, and let every other member of A get its chosen arc. Then T is an arborescence of R, and w(T) = w′(T′) + β.

*Proof.* The weights in A are w(x, y), the d(y) of π, and zeros, and w(x, y) + d(y) = w′(x, y) + β. For the structure, take S in A and follow in-arcs backwards. Off π they are chosen arcs, which stay in A by Lemma 1(b). A walk along chosen arcs cannot close a cycle, since the only one is the cycle of K, and c on it is on π, where the in-arc is not the chosen one. So the walk reaches π, and from there S_y and then x. In T′, each vertex outside A is reached from {r}, so T is an arborescence. ∎

**Lemma 3 (lower bound).** For every arborescence T of R there is an arborescence T′ after the contraction with w′(T′) ≤ w(T) − β.

*Proof.* Let Q be the path of T from {r} to c. {r} is outside A and c is in it. Let (x, y) be the first arc of Q that enters A, and let T′ be T with the arcs inside A gone, and with in-arcs into A dropped except (x, y). Since the part of Q up to x avoids A, T′ is an arborescence. Let `removed` be the total weight of the in-arcs in T of the members of A, except for (x, y). Then w′(T′) = w(T) − w(x, y) − removed + w(x, y) + d(y) − β, so it is enough that removed ≥ d(y).

If Q stays in A after y, then the arcs of Q after y are in `removed`, and they form a path from S_y to c in R[K]. So their weight is at least d(y). Otherwise let (x₂, y₂) be the last arc of Q that enters A. It is in `removed`, and so are the arcs of Q after it, which have weight at least d(y₂). If x₂ is outside K, then w(x₂, y₂) + d(y₂) ≥ β. If x₂ is in K, not in A, then w(x₂, y₂) + d(y₂) ≥ d(x₂) > β. In both cases removed ≥ β ≥ d(y). ∎

So the least weight of an arborescence falls by exactly β, and by Lemma 2 an optimum after the contraction unpacks to an optimum before it.

*Several components.* Components are vertex-disjoint. A contraction in one of them changes only the weights of arcs with head in that component, and it does not change R[K] for another K or the weights of arcs into another K. So d and β of the others stay as they are, and all contractions of a step can be applied in sequence, with the sum of their β as the total.

**Lemma 4 (halving).** One step on all active components leaves at most half as many.

*Proof.* The new chosen arc of K has its tail in another component, since u is outside K. So each active component gets a map to another component. A new active component does not hold {r}, so it is closed under this map, and it holds an old component and its image, which differ. So it holds at least two old active ones. ∎

Each cycle has at least two super-vertices and avoids {r}, so there are at most (n − 1)/2 active components at the start. So there are at most log₂(n − 1) steps with an active component.

## 4. The algorithm

1. *Start.* One call of (O) gives the set reached from r, and all else is dropped. Each v ≠ r subtracts its least in-weight from its in-arcs, and takes an arc that attains it as its chosen arc. This changes the weight of every arborescence by the same constant, and it makes all weights nonnegative. So negative weights are allowed. No in-arc of r is used.
2. *Step, while an active component exists.* In parallel for each active component K:
   - find a super-vertex c on its cycle;
   - compute d, then β and an arc that attains it;
   - contract A.
3. *End.* The chosen arcs form an arborescence of weight 0 on what is left, which is optimal since weights are nonnegative.
4. *Unpacking.* Go through the steps in reverse order and apply Lemma 2.

The weight is the sum of what Step 1 subtracted and of all β. It is part of the output, and the tree can be checked against it.

## 5. Rounds

All values are of polynomial size, since by Lemma 1(a) weights never grow.

*The cycle.* Contract each super-vertex in (M), and take the chosen arcs as meta-arcs. A spanning forest of these by Borůvka takes O(log n) steps of (M). A component with k super-vertices has k − 1 forest arcs. So if it is active, exactly one chosen arc is left out, and this arc closes a cycle, which must be the cycle of the component. Let c be its head. An aggregate over the component names c and tells whether the component holds r.

*The distances.* One call of (O) on the reversed digraph serves all components. Let K₀ = n + 1. A network edge inside a super-vertex gets weight 1 in both directions, whichever arcs H has on it. An arc (x, y) of R inside an active component gets weight K₀(K₀ w(x, y) + 1). Every other arc is removed. The offsets are 0 on the vertices of c. A shortest path has fewer than K₀ arcs, so d comes back by floor division twice. The second term K₀ · 1 counts arcs of R on the path, so a path of the shortest-path forest visits a super-vertex in one stretch: otherwise a shortcut inside it would save an arc of R. All weights are positive, so tight arcs give a forest, and each vertex stores its pointer for each step.

*The contraction.* Each vertex learns in one round the component of each neighbour. β and its arc come by an aggregate over K. Each vertex tests d(v) ≤ β, and all vertices of a super-vertex agree. A is connected, so it is a part for (M). Its new name is the name of c, and its new chosen arc goes to all its vertices. Each head computes the new weight of its in-arcs and tells the tail, in one round.

*Unpacking.* Each vertex stores, for each step, the name of its super-vertex and the chosen arc before that step. For a step, the part A knows its in-arc (x, y) by an aggregate. In the forest of that step, the path from y to c is marked by a subtree sum in (M): a vertex is on it if its subtree holds y. By Lemma 1(b) this path stays in A. An arc of it between two super-vertices is the in-arc of the later one, and it is unique by the one-stretch property, so an aggregate over that super-vertex gives it to all its vertices. All other members of A go back to their chosen arc.

At the end all super-vertices are single vertices, and each vertex knows its in-arc. There are at most log₂ n + 1 calls of (O) and Õ(1) steps of (M), which gives Õ(D). ∎

*Corollary 2.* Let M be the largest weight, after replacing w by M − w, and add a virtual root ρ with an arc of weight M to each vertex. The weight of an arborescence is then nM − w(B), for the branching B that it gives. The root ρ stays in the root component, and arcs from it never enter an oracle call, since the calls run inside active components. Its arcs are read by their heads in the aggregate for β and in Step 1. On the network, the root component falls into trees, one per chosen arc out of ρ, and such an arc marks its tree as not active, so the test for the cycle still works. A vertex whose final in-arc comes from ρ is a root of B. ∎

## 6. Checks

`sim/dmst/dmst.py` runs Sections 4 and 5 centrally on the physical graph, with Dijkstra as the oracle and the weights of Section 5. The truth is `networkx`, by a maximum branching with a large offset, and a separate plain Chu-Liu/Edmonds that computes the weight. The two agree on all runs. `networkx.minimum_spanning_arborescence` itself refused about 8% of the first instances in our runs, on digraphs that do have an arborescence, so we do not use it. Every instance passes `nx.check_planarity`. The corollary's virtual root is not planar, and only the base graph is tested for it.

| Lane | Runs | Largest n | Oracle calls | Active components | Failures |
|---|---|---|---|---|---|
| main | 154,170 | 55 | 179,086 | 441,532 | 0 |
| big | 44,714 | 128 | 66,216 | 292,159 | 0 |
| branching (Corollary 2) | 96,145 | | 126,481 | 283,118 | 0 |

Each run also asserts Lemma 1(a), the halving of Lemma 4 and the one-stretch property, and compares the tree and its weight with the truth. The largest number of steps on the random lanes is 6.

Negative controls (each breaks one step of Section 3, and each must fail):

| Control | What it breaks | Runs | Wrong tree | Wrong weight | Internal counters |
|---|---|---|---|---|---|
| `nodist` | w′ = w − β, no d(y) | 14,894 | 488 | 3,186 | crash 725, negative_weight 2,152 |
| `nobeta` | w′ = w + d(y), no β | 14,672 | 0 | 633 | weight_grew 57,505 |
| `cycleonly` | A is the cycle only | 13,977 | 343 | 340 | negative_weight 33,876, weight_grew 311 |
| `wholecomp` | A is all of K | 14,419 | 0 | 464 | crash 1,977, weight_grew 51,879 |
| `nopath` | unpacking takes chosen arcs only | 14,942 | 6,703 | 0 |  |

Steps against the bound of Lemma 4, on families built to need many steps:

| Family | n | Steps | log₂ n |
|---|---|---|---|
| `pairs` | 64 | 5 | 6.0 |
| `pairs` | 256 | 7 | 8.0 |
| `pairs` | 1,024 | 9 | 10.0 |
| `pairs` | 4,096 | 11 | 12.0 |
| `rings` | 9 | 1 | 3.2 |
| `rings` | 81 | 3 | 6.3 |
| `rings` | 729 | 5 | 9.5 |
| `rings` | 2,187 | 6 | 11.1 |
| `nested` | 100 | 1 | 6.6 |
| `nested` | 400 | 1 | 8.6 |
| `nested` | 1,600 | 1 | 10.6 |

`pairs` takes exactly ⌊log₂(n − 1)⌋ steps, so the count of Lemma 4 is tight. Oracle calls equal steps on all of them; the reach call of Step 1 comes on top.

## 7. Not covered by the checks

- Rounds and messages: there is no CONGEST simulation. The sim computes the values in the order of Section 5, and it does not route anything.
- The Exact SSSP Theorem, the Label Hypothesis and their caveats in [1]. The steps of (M) as black boxes.
- The Lean file covers the arithmetic of Lemmas 1 to 3 and the count of Lemma 4, not the graph statements or the rounds.
- The instances of the random lanes use few steps. The families `pairs` and `rings` exist to reach the bound of Lemma 4.

## References

1. S. Senge. Exact shortest paths and flows on planar graphs in CONGEST. This repository, tag `arxiv-v1`.
2. O. Fischer, R. Oshman. A distributed algorithm for directed minimum-weight spanning tree. DISC 2019, and Distributed Computing 36, 57-87.
3. M. Ghaffari, B. Haeupler. Distributed algorithms for planar networks II: low-congestion shortcuts, MST, and min-cut. SODA 2016.
4. Y. Abd-Elhaleem, M. Dory, M. Parter, O. Weimann. Distributed Maximum Flow in Planar Graphs. PODC 2025, arXiv:2411.11718.
5. C. Lenzen, H. Vahidi. Approximate minimum directed spanning trees under congestion. SIROCCO 2021.
