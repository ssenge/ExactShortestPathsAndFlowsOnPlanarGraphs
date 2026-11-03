# Small witnesses for the note-level findings, checked by plain enumeration, sharing no code with dm.cpp or lem.cpp.
import itertools
import networkx as nx


def arborescences(n, r, arcs):
    vs = [v for v in range(n) if v != r]
    ins = {v: [a for a in arcs if a[1] == v] for v in vs}
    for pick in itertools.product(*(ins[v] for v in vs)):
        par = {a[1]: a[0] for a in pick}
        ok = True
        for v in vs:
            x, g = v, 0
            while x != r and g <= n:
                x = par[x]
                g += 1
            ok = ok and x == r
        if ok:
            yield pick


def planar(arcs):
    return nx.check_planarity(nx.Graph([(a[0], a[1]) for a in arcs]))[0]


# W1. Lemma 2, proof: "c on it is on pi, where the in-arc is not the chosen one".
# r=0, cycle 1<->2 of weight 0, entry 0->1 of weight 1. Take c=2.
arcs = [(0, 1, 1), (1, 2, 0), (2, 1, 0)]
chosen = {1: (2, 1, 0), 2: (1, 2, 0)}
c = 2
d = {1: 0, 2: 0}
beta = 1          # 0->1 has w + d(1) = 1
pi = [(1, 2, 0)]  # the only path from S_y = {1} to c
T = {1: (0, 1, 1), 2: pi[0]}
assert T[c] == chosen[c], 'the in-arc of c on pi IS its chosen arc'
assert sum(a[2] for a in T.values()) == min(sum(a[2] for a in t) for t in arborescences(3, 0, arcs))
assert planar(arcs)
print('W1 ok: the in-arc of c on pi is the chosen arc of c, and T is an optimal arborescence', T)

# W2. Section 5: the same instance. One network edge {1,2} carries both chosen arcs. As network edges
# the component with k=2 has one edge, k-1 of them, so nothing is left out. Only per arc is one left out.
chosen_arcs = [(1, 2), (2, 1)]
net_edges = {frozenset(a) for a in chosen_arcs}
assert len(net_edges) == 1 and len(chosen_arcs) == 2
print('W2 ok: 2 chosen arcs on', len(net_edges), 'network edge; a forest of network edges leaves none out')

# W3. Section 3, "Several components": after contracting K1, K2 is not a weak component any more.
# r=0; K1={1,2} and K2={3,4} are 2-cycles of weight 0; the entry of K1 comes from K2, the entry of K2 from r.
arcs = [(1, 2, 0), (2, 1, 0), (3, 4, 0), (4, 3, 0), (3, 1, 1), (0, 4, 5), (0, 1, 9)]
assert planar(arcs)
# K1: c=1, d(1)=d(2)=0, least entering value: 3->1 with 1. So the new chosen arc of A1={1,2} has tail 3, in K2.
# After that the chosen arcs join A1 with {3,4}: the weak component is {A1,3,4}, and K2 alone is not one.
G = nx.Graph([('A1', 3), (3, 4)])   # chosen arcs after the contraction of K1: 3->A1, 3->4, 4->3
assert sorted(map(str, nx.node_connected_component(G, 3))) == ['3', '4', 'A1']
# What the note wants for K2: its own d and beta, unchanged. Direct check that doing so is right.
best = min(sum(a[2] for a in t) for t in arborescences(5, 0, arcs))
beta1, beta2 = 1, 5        # K2: c=4, d(4)=d(3)=0, entering 0->4 with 5
# weights after both: 3->1 is 0 (chosen), 0->1 is 9-1=8, 0->4 is 0, and the tree on {r, A1, A2} has weight 0
assert best == beta1 + beta2, (best, beta1, beta2)
print('W3 ok: K2 is no weak component after K1 is contracted; the betas still sum to the optimum', best)

# W4. Every super-vertex is strongly connected in H: a member of A reaches c along pi and is reached from the
# cycle along chosen arcs. So the "both directions" of Section 5 is more than is needed. See sv_not_strong in the lanes.
print('W4: see sv_strong and sv_not_strong in the lanes')
