// Independent harness for notes/DMST.md. Written from the note's text, does not use dmst.py.
//
// Physical level: network edges, arcs, super-vertices. Oracle: Dijkstra on the reversed digraph with the weights of Section 5, with a
// RANDOM tight arc as pointer at each vertex. Ties in chosen arcs, in the arc of beta and in the Boruvka order are random.
// Truth: brute force over all in-arc choices when small, and a plain array-based Chu-Liu that uses no code from the algorithm below.
//
// Usage:
//   check_dmst exh <seed>                exhaustive small networks and weight alphabets
//   check_dmst rnd <seed> <seconds> <maxn>   random planar networks
//   check_dmst cor <seed> <seconds> <maxn>   Corollary 2, on the network, with the virtual root outside it
//   check_dmst ctl <seed> <seconds>      negative controls of this harness
//   check_dmst fam                       long families, steps against the bound
//   check_dmst dump <seed> <count>       writes sample networks for a planarity check in python
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
typedef long long ll;
static const ll INF = LLONG_MAX / 4;

struct Arc { int u, v; ll w; };
struct Inst { int n; vector<pair<int,int>> edges; vector<Arc> arcs; int r; };

typedef mt19937_64 RNG;
static int ri(RNG& g, int a, int b) { return a + (int)(g() % (unsigned long long)(b - a + 1)); }

// ---------- truth ----------
static ll chuliu(int n, int root, vector<array<ll,3>> E) {
    ll res = 0;
    vector<ll> in(n); vector<int> pre(n), id(n), vis(n);
    while (true) {
        fill(in.begin(), in.begin() + n, INF);
        for (auto& e : E) if (e[0] != e[1] && e[2] < in[e[1]]) { in[e[1]] = e[2]; pre[e[1]] = (int)e[0]; }
        for (int i = 0; i < n; i++) if (i != root && in[i] == INF) return INF;
        int cnt = 0;
        fill(id.begin(), id.begin() + n, -1); fill(vis.begin(), vis.begin() + n, -1);
        in[root] = 0;
        for (int i = 0; i < n; i++) {
            res += in[i];
            int v = i;
            while (vis[v] != i && id[v] == -1 && v != root) { vis[v] = i; v = pre[v]; }
            if (v != root && id[v] == -1) {
                for (int u = pre[v]; u != v; u = pre[u]) id[u] = cnt;
                id[v] = cnt++;
            }
        }
        if (cnt == 0) break;
        for (int i = 0; i < n; i++) if (id[i] == -1) id[i] = cnt++;
        for (auto& e : E) {
            int v = (int)e[1];
            e[0] = id[e[0]]; e[1] = id[e[1]];
            if (e[0] != e[1]) e[2] -= in[v];
        }
        n = cnt; root = id[root];
    }
    return res;
}

// All in-arc choices. Returns INF if there is none, or -INF as "too big".
static ll brute(int N, int r, const vector<int>& verts, const vector<Arc>& arcs, ll limit) {
    vector<vector<int>> in(N);
    for (int i = 0; i < (int)arcs.size(); i++) in[arcs[i].v].push_back(i);
    vector<int> who;
    double prod = 1;
    for (int v : verts) if (v != r) { who.push_back(v); prod *= max<size_t>(1, in[v].size()); if (in[v].empty()) return INF; }
    if (prod > (double)limit) return -INF;
    vector<int> par(N, -1);
    ll best = INF;
    vector<int> st(N, 0);
    int stamp = 0;
    function<void(int, ll)> rec = [&](int i, ll cost) {
        if (i == (int)who.size()) {
            for (int v : who) {
                stamp++;
                int x = v;
                while (x != r) { if (st[x] == stamp) return; st[x] = stamp; x = par[x]; }
            }
            best = min(best, cost);
            return;
        }
        for (int e : in[who[i]]) { par[who[i]] = arcs[e].u; rec(i + 1, cost + arcs[e].w); }
    };
    rec(0, 0);
    return best;
}

// ---------- the algorithm of the note ----------
enum Ctl { OK = 0, STRICT, NOSECOND, SMALLK, NODIST, NOBETA, NOPATH, CYCLEONLY, WHOLE };

struct Stats {
    map<string, ll> c;
    void add(const string& k, ll v = 1) { c[k] += v; }
    void mx(const string& k, ll v) { auto it = c.find(k); if (it == c.end() || it->second < v) c[k] = v; }
};

struct Result { bool ok = true; string why; ll total = 0; vector<int> inarc; int steps = 0; int calls = 0; };

struct Level {
    vector<int> sid;           // super-vertex name of each vertex before the step
    vector<int> chosen;        // chosen arc of each name before the step
    vector<int> ptr, ptrArc;   // pointer of the forest of the step
    vector<ll> val;
    vector<pair<int, vector<int>>> groups;   // new name, members
};

#define FAILS(msg) do { res.ok = false; res.why = msg; return res; } while (0)

// `virt`: arcs out of vertex n are from the virtual root rho, which is not on the network. Network tests run on the vertices 0..n-1.
static Result solve(const Inst& I, RNG& g, Stats& st, Ctl ctl, bool virt, bool heavy) {
    Result res;
    const int n = I.n, N = n + (virt ? 1 : 0), r = I.r;
    vector<Arc> A = I.arcs;
    int m = (int)A.size();
    vector<char> alive(m, 1);
    // Step 1: reach
    vector<char> reached(N, 0);
    {
        vector<vector<int>> out(N);
        for (auto& a : A) out[a.u].push_back(a.v);
        vector<int> q{r}; reached[r] = 1;
        while (!q.empty()) { int x = q.back(); q.pop_back(); for (int y : out[x]) if (!reached[y]) { reached[y] = 1; q.push_back(y); } }
    }
    if (!virt) res.calls++;
    vector<int> sid(N, -1);
    int nreach = 0;
    for (int v = 0; v < N; v++) if (reached[v]) { sid[v] = v; nreach++; }
    if (nreach < n + (virt ? 1 : 0)) st.add("n.instances_with_dropped");
    for (int e = 0; e < m; e++) if (!reached[A[e].u] || !reached[A[e].v] || A[e].v == r) alive[e] = 0;
    vector<ll> mn(N, INF);
    for (int e = 0; e < m; e++) if (alive[e]) mn[A[e].v] = min(mn[A[e].v], A[e].w);
    vector<int> chosen(N, -1), cnt(N, 0);
    for (int v = 0; v < N; v++) if (reached[v] && v != r) { if (mn[v] == INF) FAILS("reached vertex without in-arc"); res.total += mn[v]; }
    for (int e = 0; e < m; e++) if (alive[e]) {
        A[e].w -= mn[A[e].v];
        if (A[e].w == 0) { int v = A[e].v; cnt[v]++; if ((int)(g() % cnt[v]) == 0) chosen[v] = e; }
    }
    vector<Level> levels;
    int lastActive = -1;
    int maxSteps = 0;
    { int nn = nreach; while ((1LL << (maxSteps + 1)) <= (ll)(nn - 1)) maxSteps++; if (nn <= 2) maxSteps = 0; }
    // adjacency of the network
    vector<vector<int>> nbr(n);
    for (auto& e : I.edges) { nbr[e.first].push_back(e.second); nbr[e.second].push_back(e.first); }

    while (true) {
        // ---- components by a spanning forest of the chosen meta-arcs (network arcs only)
        vector<int> dsu(N); iota(dsu.begin(), dsu.end(), 0);
        function<int(int)> fnd = [&](int x) { while (dsu[x] != x) { dsu[x] = dsu[dsu[x]]; x = dsu[x]; } return x; };
        vector<int> names;
        { vector<char> seen(N, 0); for (int v = 0; v < N; v++) if (sid[v] >= 0 && !seen[sid[v]]) { seen[sid[v]] = 1; names.push_back(sid[v]); } }
        vector<int> order;
        for (int s : names) if (s != r) order.push_back(s);
        shuffle(order.begin(), order.end(), g);
        vector<int> leftout;
        vector<char> rhoArc(N, 0);
        for (int s : order) {
            int e = chosen[s];
            int t = A[e].u;
            if (virt && t == n) { rhoArc[s] = 1; continue; }
            int a = fnd(sid[t]), b = fnd(s);
            if (a == b) leftout.push_back(s); else dsu[a] = b;
        }
        map<int, vector<int>> comp;
        for (int s : names) if (!(virt && s == n)) comp[fnd(s)].push_back(s);
        map<int, int> headOf; map<int,int> lo;
        for (int s : leftout) { lo[fnd(s)]++; headOf[fnd(s)] = s; }
        struct Act { int c; vector<int> mem; vector<int> cyc; };
        vector<Act> act;
        for (auto& kv : comp) {
            bool isRoot = false;
            if (!virt) isRoot = (fnd(sid[r]) == kv.first);
            else for (int s : kv.second) if (rhoArc[s]) isRoot = true;
            if (isRoot) {
                if (lo.count(kv.first)) FAILS("root component has a left-out arc");
                if (virt) { int cntr = 0; for (int s : kv.second) cntr += rhoArc[s]; if (cntr != 1) FAILS("tree with several arcs from rho"); }
                continue;
            }
            if (lo[kv.first] != 1) FAILS("active component without exactly one left-out arc");
            Act a; a.c = headOf[kv.first]; a.mem = kv.second;
            int x = a.c, steps = 0;
            do {
                a.cyc.push_back(x);
                x = sid[A[chosen[x]].u];
                if (++steps > (int)a.mem.size() + 1) FAILS("head of the left-out arc is not on a cycle");
            } while (x != a.c);
            if (a.cyc.size() < 2) FAILS("cycle of one super-vertex");
            act.push_back(a);
        }
        if (act.empty()) break;
        res.steps++;
        st.add("n.active", act.size());
        if (res.steps > maxSteps) FAILS("steps above floor(log2(n-1))");
        if (lastActive >= 0 && 2 * (int)act.size() > lastActive) FAILS("no halving");
        lastActive = (int)act.size();
        res.calls++;

        // ---- oracle, reversed, physical
        vector<int> compId(N, -1);
        for (int i = 0; i < (int)act.size(); i++) for (int s : act[i].mem) compId[s] = i;
        ll K0 = n + 1;
        if (ctl == SMALLK) K0 = 2;
        struct RE { int to; ll w; int arc; };
        vector<vector<RE>> radj(n);
        for (auto& e : I.edges) {
            int a = e.first, b = e.second;
            if (sid[a] >= 0 && sid[a] == sid[b]) { radj[a].push_back({b, 1, -1}); radj[b].push_back({a, 1, -1}); }
        }
        for (int e = 0; e < m; e++) if (alive[e]) {
            int x = A[e].u, y = A[e].v;
            if (virt && x == n) continue;
            int sx = sid[x], sy = sid[y];
            if (sx != sy && compId[sx] >= 0 && compId[sx] == compId[sy]) {
                ll wt = (ctl == NOSECOND) ? K0 * K0 * A[e].w + 1 : K0 * (K0 * A[e].w + 1);
                radj[y].push_back({x, wt, e});
            }
        }
        vector<ll> val(n, INF);
        typedef pair<ll,int> P;
        priority_queue<P, vector<P>, greater<P>> pq;
        vector<char> isC(N, 0);
        for (auto& a : act) isC[a.c] = 1;
        for (int v = 0; v < n; v++) if (sid[v] >= 0 && isC[sid[v]]) { val[v] = 0; pq.push({0, v}); }
        while (!pq.empty()) {
            auto [dv, v] = pq.top(); pq.pop();
            if (dv != val[v]) continue;
            for (auto& re : radj[v]) if (dv + re.w < val[re.to]) { val[re.to] = dv + re.w; pq.push({val[re.to], re.to}); }
        }
        vector<int> ptr(n, -1), ptrArc(n, -2), cntT(n, 0);
        for (int y = 0; y < n; y++) if (val[y] < INF) for (auto& re : radj[y]) if (val[y] + re.w == val[re.to]) {
            cntT[re.to]++;
            if ((int)(g() % cntT[re.to]) == 0) { ptr[re.to] = y; ptrArc[re.to] = re.arc; }
        }
        for (int v = 0; v < n; v++) {
            if (val[v] == 0 && ptr[v] != -1) FAILS("source with a tight arc");
            if (val[v] > 0 && val[v] < INF && ptr[v] == -1) FAILS("no tight arc");
        }
        // ---- d by decoding, against d computed separately on the meta level
        vector<ll> dM(N, INF);
        {
            vector<vector<pair<int,ll>>> into(N);
            for (int e = 0; e < m; e++) if (alive[e]) {
                int x = A[e].u, y = A[e].v;
                if (virt && x == n) continue;
                int sx = sid[x], sy = sid[y];
                if (sx != sy && compId[sx] >= 0 && compId[sx] == compId[sy]) into[sy].push_back({sx, A[e].w});
            }
            priority_queue<P, vector<P>, greater<P>> pq2;
            for (auto& a : act) { dM[a.c] = 0; pq2.push({0, a.c}); }
            while (!pq2.empty()) {
                auto [dv, v] = pq2.top(); pq2.pop();
                if (dv != dM[v]) continue;
                for (auto& pr : into[v]) if (dv + pr.second < dM[pr.first]) { dM[pr.first] = dv + pr.second; pq2.push({dM[pr.first], pr.first}); }
            }
        }
        vector<ll> dDec(N, -1);
        for (int v = 0; v < n; v++) if (sid[v] >= 0 && compId[sid[v]] >= 0) {
            ll dv = val[v] >= INF ? INF : val[v] / K0 / K0;
            if (dDec[sid[v]] == -1) dDec[sid[v]] = dv;
            else if (dDec[sid[v]] != dv) FAILS("vertices of a super-vertex disagree on d");
            if (dv != dM[sid[v]]) FAILS("decoded d differs from the meta-level d");
            if (val[v] < INF) st.add("chk.decode");
        }
        // ---- one stretch, on every forest path, not only those used
        if (heavy) {
            vector<int> stamp(N, -1);
            for (int v = 0; v < n; v++) if (val[v] < INF && sid[v] >= 0 && compId[sid[v]] >= 0) {
                int x = v, cur = sid[v];
                stamp[cur] = v;
                while (ptr[x] != -1) {
                    int y = ptr[x];
                    if (sid[y] != cur) {
                        if (stamp[sid[y]] == v) FAILS("forest path re-enters a super-vertex");
                        cur = sid[y]; stamp[cur] = v;
                        st.add("chk.onestretch_arcs");
                    }
                    x = y;
                }
                if (!isC[sid[x]]) FAILS("forest path does not end in c");
            }
        }
        // ---- beta and its arc
        int na = (int)act.size();
        vector<ll> beta(na, INF); vector<int> bArc(na, -1), bCnt(na, 0);
        for (int e = 0; e < m; e++) if (alive[e]) {
            int y = A[e].v, sy = sid[y], i = compId[sy];
            if (i < 0) continue;
            int x = A[e].u;
            int cx = compId[sid[x]];
            if (cx == i) continue;
            if (dM[sy] >= INF && ctl != NODIST) continue;
            ll b = A[e].w + (ctl == NODIST ? 0 : dM[sy]);
            if (b < beta[i]) { beta[i] = b; bArc[i] = e; bCnt[i] = 1; }
            else if (b == beta[i]) { bCnt[i]++; if ((int)(g() % bCnt[i]) == 0) bArc[i] = e; }
        }
        vector<char> inA(N, 0);
        Level L; L.sid = sid; L.chosen = chosen; L.ptr = ptr; L.ptrArc = ptrArc; L.val = val;
        vector<ll> opt_before_w;
        ll optBefore = 0;
        auto metaOpt = [&](const vector<int>& sidx, const vector<ll>* wx, const vector<char>* alx) -> ll {
            map<int,int> idx;
            for (int v = 0; v < N; v++) if (sidx[v] >= 0 && !idx.count(sidx[v])) { int t = (int)idx.size(); idx[sidx[v]] = t; }
            vector<array<ll,3>> E;
            for (int e = 0; e < m; e++) if ((*alx)[e] && sidx[A[e].u] >= 0 && sidx[A[e].v] >= 0 && sidx[A[e].u] != sidx[A[e].v]) E.push_back({(ll)idx[sidx[A[e].u]], (ll)idx[sidx[A[e].v]], (*wx)[e]});
            return chuliu((int)idx.size(), idx[sidx[r]], E);
        };
        vector<ll> wNow(m); for (int e = 0; e < m; e++) wNow[e] = A[e].w;
        if (heavy) optBefore = metaOpt(sid, &wNow, &alive);
        bool anyPartial = false, anyCycOnly = false, anyWhole = false;
        for (int i = 0; i < na; i++) {
            if (bArc[i] < 0 || beta[i] >= INF) FAILS("beta not finite");
            auto& a = act[i];
            for (int s : a.mem) {
                bool in = dM[s] <= beta[i];
                if (ctl == STRICT) in = dM[s] < beta[i];
                if (ctl == WHOLE) in = true;
                if (ctl == CYCLEONLY) in = false;
                if (in) inA[s] = 1;
            }
            for (int s : a.cyc) inA[s] = 1;
            int cntA = 0;
            for (int s : a.mem) cntA += inA[s];
            if (cntA < (int)a.mem.size()) anyPartial = true; else anyWhole = true;
            if (cntA == (int)a.cyc.size()) anyCycOnly = true;
            if (cntA > (int)a.cyc.size() && cntA < (int)a.mem.size()) st.add("n.A_strictly_between");
            else if (cntA == (int)a.mem.size()) st.add("n.A_is_K");
            else st.add("n.A_is_cycle");
            if (ctl == OK) {
                if (!inA[sid[A[bArc[i]].v]]) FAILS("head of the beta arc not in A");
                for (int s : a.mem) if (inA[s] && !inA[sid[A[chosen[s]].u]]) FAILS("chosen arc of a member of A has its tail outside A");
                // A connected on the network
                vector<int> st2; set<int> seen;
                st2.push_back(0);
                int start = -1, total = 0;
                for (int v = 0; v < n; v++) if (sid[v] >= 0 && compId[sid[v]] == i && inA[sid[v]]) { total++; if (start < 0) start = v; }
                st2.clear(); st2.push_back(start); seen.insert(start);
                while (!st2.empty()) {
                    int v = st2.back(); st2.pop_back();
                    for (int y : nbr[v]) if (sid[y] >= 0 && compId[sid[y]] == i && inA[sid[y]] && !seen.count(y)) { seen.insert(y); st2.push_back(y); }
                }
                if ((int)seen.size() != total) FAILS("A not connected on the network");
            }
            res.total += beta[i];
        }
        (void)anyPartial; (void)anyCycOnly; (void)anyWhole;
        // groups
        for (int i = 0; i < na; i++) {
            vector<int> mem;
            for (int s : act[i].mem) if (inA[s]) mem.push_back(s);
            L.groups.push_back({act[i].c, mem});
            st.add("n.members_contracted", mem.size());
        }
        // ---- several components, one after the other, each with the d and beta of the start of the step
        if (heavy && ctl == OK && na > 1) {
            vector<int> sq = sid; vector<ll> wq = wNow; vector<char> aq = alive;
            ll prev = optBefore;
            for (int i = 0; i < na; i++) {
                for (int e = 0; e < m; e++) if (aq[e]) {
                    int sy0 = sid[A[e].v];
                    if (compId[sy0] == i && inA[sy0]) {
                        int sx0 = sid[A[e].u];
                        if (compId[sx0] == i && inA[sx0]) aq[e] = 0;
                        else wq[e] = wq[e] + dM[sy0] - beta[i];
                    }
                }
                for (int v = 0; v < N; v++) if (sid[v] >= 0 && compId[sid[v]] == i && inA[sid[v]]) sq[v] = act[i].c;
                ll now = metaOpt(sq, &wq, &aq);
                if (prev - now != beta[i]) FAILS("sequential contraction: optimum did not fall by beta");
                prev = now;
                st.add("chk.sequential");
            }
        }
        // ---- apply
        for (int e = 0; e < m; e++) if (alive[e]) {
            int y = A[e].v, sy = sid[y];
            if (compId[sy] < 0 || !inA[sy]) continue;
            int i = compId[sy];
            int x = A[e].u, sx = sid[x];
            if (compId[sx] == i && inA[sx]) { alive[e] = 0; continue; }
            if (dM[sy] >= INF) FAILS("member of A with infinite d");
            ll nw = A[e].w + (ctl == NODIST ? 0 : dM[sy]) - (ctl == NOBETA ? 0 : beta[i]);
            if (nw < 0) FAILS("new weight negative");
            if (ctl == OK || ctl == NODIST || ctl == NOBETA) {
                if (nw < 0) FAILS("new weight negative");
                if (nw > A[e].w) FAILS("new weight above the old one");
                if (ctl == OK && compId[sx] == i && nw <= 0) FAILS("arc from K minus A not positive");
            }
            A[e].w = nw;
        }
        vector<int> newName(N, -1);
        for (int i = 0; i < na; i++) for (int s : act[i].mem) if (inA[s]) newName[s] = act[i].c;
        for (int i = 0; i < na; i++) for (int s : act[i].mem) if (inA[s]) chosen[s] = -1;
        for (int i = 0; i < na; i++) chosen[act[i].c] = bArc[i];
        for (int v = 0; v < N; v++) if (sid[v] >= 0 && newName[sid[v]] >= 0) sid[v] = newName[sid[v]];
        levels.push_back(std::move(L));
        if (ctl != OK && ctl != STRICT && ctl != CYCLEONLY && ctl != WHOLE && ctl != NOPATH && ctl != NOSECOND && ctl != SMALLK) {
            // controls that change weights: chosen arcs may not be zero; the final check will tell
        }
        // ---- it is still a state
        if (ctl == OK) {
            for (int v = 0; v < N; v++) if (sid[v] >= 0 && sid[v] == v) { /* names need not be vertices of the set: checked below */ }
            vector<char> isName(N, 0);
            for (int v = 0; v < N; v++) if (sid[v] >= 0) isName[sid[v]] = 1;
            if (sid[r] != r) FAILS("root merged");
            for (int s = 0; s < N; s++) if (isName[s] && s != r) {
                int e = chosen[s];
                if (e < 0 || !alive[e]) FAILS("no chosen arc");
                if (A[e].w != 0) FAILS("chosen arc not of weight 0");
                if (sid[A[e].v] != s) FAILS("chosen arc has wrong head");
                if (sid[A[e].u] == s) FAILS("chosen arc inside its super-vertex");
            }
            for (int e = 0; e < m; e++) if (alive[e]) {
                if (A[e].w < 0) FAILS("negative weight in the state");
                if (sid[A[e].u] == sid[A[e].v]) FAILS("alive arc inside a super-vertex");
            }
            // every super-vertex reached from {r}
            vector<vector<int>> out(N);
            for (int e = 0; e < m; e++) if (alive[e]) out[sid[A[e].u]].push_back(sid[A[e].v]);
            vector<char> seen(N, 0); vector<int> q{r}; seen[r] = 1;
            while (!q.empty()) { int x = q.back(); q.pop_back(); for (int y : out[x]) if (!seen[y]) { seen[y] = 1; q.push_back(y); } }
            for (int s = 0; s < N; s++) if (isName[s] && !seen[s]) FAILS("super-vertex not reached from r");
            // every super-vertex connected on the network
            if (heavy) {
                for (int s = 0; s < N; s++) if (isName[s] && s != n) {
                    int start = -1, total = 0;
                    for (int v = 0; v < n; v++) if (sid[v] == s) { total++; if (start < 0) start = v; }
                    vector<int> st2{start}; set<int> sn{start};
                    while (!st2.empty()) { int v = st2.back(); st2.pop_back(); for (int y : nbr[v]) if (sid[y] == s && !sn.count(y)) { sn.insert(y); st2.push_back(y); } }
                    if ((int)sn.size() != total) FAILS("super-vertex not connected on the network");
                }
                vector<ll> wAfter(m); for (int e = 0; e < m; e++) wAfter[e] = A[e].w;
                ll optAfter = metaOpt(sid, &wAfter, &alive);
                ll sumB = 0; for (int i = 0; i < na; i++) sumB += beta[i];
                if (optBefore - optAfter != sumB) FAILS("optimum did not fall by the sum of beta");
                st.add("chk.opt_step");
            }
        }
    }
    // ---- end: chosen arcs form a tree of weight 0
    // ---- unpacking
    vector<int> T = chosen;
    for (int li = (int)levels.size() - 1; li >= 0; li--) {
        Level& L = levels[li];
        // subtree sums on the forest of the step: all y of this step at once, as one run of (T2)
        vector<ll> sum(n, 0);
        vector<int> headOfGroup;
        for (auto& g2 : L.groups) {
            int e = T[g2.first];
            if (e < 0) FAILS("group without in-arc");
            int y = A[e].v;
            sum[y] += 1;
        }
        vector<int> ord;
        for (int v = 0; v < n; v++) if (L.val[v] < INF) ord.push_back(v);
        sort(ord.begin(), ord.end(), [&](int a, int b) { return L.val[a] > L.val[b]; });
        for (int v : ord) if (L.ptr[v] != -1) sum[L.ptr[v]] += sum[v];
        map<int,int> newIn;   // super-vertex of the old partition -> arc
        for (int v : ord) if (sum[v] > 0 && L.ptr[v] != -1) {
            int b = L.ptr[v];
            if (L.sid[v] != L.sid[b]) {
                int sb = L.sid[b];
                if (newIn.count(sb) && ctl == OK) FAILS("two marked arcs into one super-vertex: not one stretch");
                if (newIn.count(sb)) { res.ok = false; res.why = "reentry"; return res; }
                newIn[sb] = L.ptrArc[v];
                st.add("n.path_arcs");
            }
        }
        for (int v = 0; v < n; v++) if (sum[v] > 1) FAILS("two y in one tree of the forest");
        for (auto& g2 : L.groups) {
            int e = T[g2.first];
            int y = A[e].v, Sy = L.sid[y];
            bool holds = false;
            for (int s : g2.second) if (s == Sy) holds = true;
            if (!holds) { res.ok = false; res.why = "S_y not in A"; return res; }
            for (int s : g2.second) T[s] = L.chosen[s];
            if (ctl != NOPATH) for (int s : g2.second) { auto it = newIn.find(s); if (it != newIn.end()) T[s] = it->second; }
            if (ctl == OK && newIn.count(Sy)) FAILS("S_y entered again by its path");
            T[Sy] = e;
        }
        if (ctl == OK) for (auto& kv : newIn) {
            bool isMem = false;
            for (auto& g2 : L.groups) for (int s : g2.second) if (s == kv.first) isMem = true;
            if (!isMem) FAILS("marked arc into a super-vertex outside A");
        }
    }
    res.inarc.assign(N, -1);
    for (int v = 0; v < N; v++) if (reached[v] && v != r) {
        int e = T[v];
        if (e < 0) { res.ok = false; res.why = "no in-arc after unpacking"; return res; }
        res.inarc[v] = e;
    }
    return res;
}

// ---------- check against the truth ----------
// returns false on failure; prints the instance when loud
static bool check(const Inst& I, const Result& R, Stats& st, bool virt, ll bruteLimit, const char* tag, bool loud) {
    auto fail = [&](const string& why) {
        st.add(string("FAIL.") + why);
        if (loud) {
            printf("FAIL %s %s n=%d r=%d\n", tag, why.c_str(), I.n, I.r);
            if (I.n <= 12) { for (auto& a : I.arcs) printf(" (%d,%d,%lld)", a.u, a.v, a.w); printf("\n"); for (auto& e : I.edges) printf(" {%d,%d}", e.first, e.second); printf("\n"); }
            fflush(stdout);
        }
        return false;
    };
    if (!R.ok) return fail(R.why);
    const int N = I.n + (virt ? 1 : 0), r = I.r;
    vector<char> reached(N, 0);
    {
        vector<vector<int>> out(N);
        for (auto& a : I.arcs) out[a.u].push_back(a.v);
        vector<int> q{r}; reached[r] = 1;
        while (!q.empty()) { int x = q.back(); q.pop_back(); for (int y : out[x]) if (!reached[y]) { reached[y] = 1; q.push_back(y); } }
    }
    vector<int> idx(N, -1); int cnt = 0; vector<int> verts;
    for (int v = 0; v < N; v++) if (reached[v]) { idx[v] = cnt++; verts.push_back(v); }
    vector<array<ll,3>> E; vector<Arc> arcsR;
    for (auto& a : I.arcs) if (reached[a.u] && reached[a.v] && a.v != r) { E.push_back({(ll)idx[a.u], (ll)idx[a.v], a.w}); arcsR.push_back(a); }
    ll truth = chuliu(cnt, idx[r], E);
    if (bruteLimit > 0) {
        ll b = brute(N, r, verts, arcsR, bruteLimit);
        if (b != -INF) { st.add("chk.brute"); if (b != truth) return fail("TRUTHS_DIFFER"); }
    }
    // tree
    ll w = 0;
    for (int v : verts) if (v != r) {
        int e = R.inarc[v];
        if (e < 0 || I.arcs[e].v != v) return fail("arc_not_into_vertex");
        if (!reached[I.arcs[e].u]) return fail("tail_not_reached");
        w += I.arcs[e].w;
    }
    for (int v : verts) {
        int x = v, c = 0;
        while (x != r) { x = I.arcs[R.inarc[x]].u; if (++c > N) return fail("not_a_tree"); }
    }
    if (w != truth) return fail("tree_weight");
    if (R.total != truth) return fail("reported_weight");
    st.add("runs");
    st.mx("max.steps", R.steps);
    st.mx("max.n", I.n);
    st.add(string("steps.") + to_string(R.steps));
    return true;
}

// ---------- networks: planar by construction ----------
struct Net { int n; vector<pair<int,int>> e; };
static Net dedup(int n, vector<pair<int,int>> e) {
    set<pair<int,int>> s;
    for (auto& p : e) if (p.first != p.second) s.insert({min(p.first, p.second), max(p.first, p.second)});
    return {n, vector<pair<int,int>>(s.begin(), s.end())};
}
static Net connected_part(Net N) {
    vector<vector<int>> a(N.n);
    for (auto& e : N.e) { a[e.first].push_back(e.second); a[e.second].push_back(e.first); }
    vector<int> comp(N.n, -1); int best = -1, bestc = -1, c = 0;
    for (int s = 0; s < N.n; s++) if (comp[s] < 0) {
        int sz = 0; vector<int> q{s}; comp[s] = c;
        while (!q.empty()) { int x = q.back(); q.pop_back(); sz++; for (int y : a[x]) if (comp[y] < 0) { comp[y] = c; q.push_back(y); } }
        if (sz > best) { best = sz; bestc = c; }
        c++;
    }
    vector<int> id(N.n, -1); int k = 0;
    for (int v = 0; v < N.n; v++) if (comp[v] == bestc) id[v] = k++;
    vector<pair<int,int>> E;
    for (auto& e : N.e) if (comp[e.first] == bestc && comp[e.second] == bestc) E.push_back({id[e.first], id[e.second]});
    return {k, E};
}
static Net network(RNG& g, int maxn) {
    int kind = ri(g, 0, 11);
    int rt = max(2, (int)sqrt((double)maxn));
    vector<pair<int,int>> E;
    switch (kind) {
    case 0: { // grid with diagonals and holes
        int a = ri(g, 2, rt), b = ri(g, 2, rt);
        double drop = (g() % 3) * 0.15, dg = (g() % 3) * 0.4;
        for (int i = 0; i < a; i++) for (int j = 0; j < b; j++) {
            int x = i * b + j;
            if (j + 1 < b && (g() % 1000) / 1000.0 >= drop) E.push_back({x, x + 1});
            if (i + 1 < a && (g() % 1000) / 1000.0 >= drop) E.push_back({x, x + b});
            if (i + 1 < a && j + 1 < b && (g() % 1000) / 1000.0 < dg) { if (g() & 1) E.push_back({x, x + b + 1}); else E.push_back({x + 1, x + b}); }
        }
        return connected_part(dedup(a * b, E));
    }
    case 1: { // rings with spokes and a centre
        int rings = ri(g, 1, max(1, rt / 2)), len = ri(g, 3, max(3, rt));
        int n = 1 + rings * len;
        for (int i = 0; i < rings; i++) for (int j = 0; j < len; j++) {
            int x = 1 + i * len + j;
            E.push_back({x, 1 + i * len + (j + 1) % len});
            if (i == 0) E.push_back({0, x});
            else if (g() % 3) E.push_back({x, x - len});
        }
        return connected_part(dedup(n, E));
    }
    case 2: { // stacked triangulation
        int n = ri(g, 4, max(4, maxn));
        vector<array<int,3>> F{{0,1,2},{0,1,2}};
        E = {{0,1},{0,2},{1,2}};
        for (int v = 3; v < n; v++) {
            int i = (int)(g() % F.size());
            auto f = F[i];
            F[i] = {f[0], f[1], v};
            F.push_back({f[1], f[2], v}); F.push_back({f[0], f[2], v});
            E.push_back({f[0], v}); E.push_back({f[1], v}); E.push_back({f[2], v});
        }
        double drop = (g() % 3) * 0.2;
        vector<pair<int,int>> E2;
        for (auto& e : E) if ((g() % 1000) / 1000.0 >= drop) E2.push_back(e);
        return connected_part(dedup(n, E2));
    }
    case 3: { // wheel
        int n = ri(g, 4, max(4, maxn));
        for (int v = 1; v < n; v++) { E.push_back({0, v}); E.push_back({v, v + 1 < n ? v + 1 : 1}); }
        return dedup(n, E);
    }
    case 4: { // cycle
        int n = ri(g, 3, max(3, maxn));
        for (int v = 0; v < n; v++) E.push_back({v, (v + 1) % n});
        return dedup(n, E);
    }
    case 5: { // path
        int n = ri(g, 2, max(2, maxn));
        for (int v = 1; v < n; v++) E.push_back({v - 1, v});
        return dedup(n, E);
    }
    case 6: { // tree
        int n = ri(g, 2, max(2, maxn));
        int span = ri(g, 1, 6);
        for (int v = 1; v < n; v++) E.push_back({ri(g, max(0, v - span), v - 1), v});
        return dedup(n, E);
    }
    case 7: { // triangulated polygon
        int n = ri(g, 3, max(3, maxn));
        for (int v = 0; v < n; v++) E.push_back({v, (v + 1) % n});
        function<void(int,int)> rec = [&](int a, int b) { // polygon a..b
            if (b - a < 2) return;
            int m = ri(g, a + 1, b - 1);
            if (a != m - 0 && m - a > 1) E.push_back({a, m});
            if (b - m > 1) E.push_back({m, b});
            rec(a, m); rec(m, b);
        };
        rec(0, n - 1);
        return dedup(n, E);
    }
    case 8: { // ladder
        int k = ri(g, 2, max(2, maxn / 2));
        for (int i = 0; i < k; i++) { E.push_back({2 * i, 2 * i + 1}); if (i + 1 < k) { E.push_back({2 * i, 2 * i + 2}); E.push_back({2 * i + 1, 2 * i + 3}); } }
        return dedup(2 * k, E);
    }
    case 9: { // K_{2,k}
        int k = ri(g, 2, max(2, maxn - 2));
        for (int i = 0; i < k; i++) { E.push_back({0, 2 + i}); E.push_back({1, 2 + i}); }
        return dedup(2 + k, E);
    }
    case 10: { // nested triangles
        int k = ri(g, 1, max(1, maxn / 3));
        for (int i = 0; i < k; i++) {
            for (int j = 0; j < 3; j++) { E.push_back({3 * i + j, 3 * i + (j + 1) % 3}); if (i + 1 < k) E.push_back({3 * i + j, 3 * i + 3 + j}); }
        }
        return dedup(3 * k, E);
    }
    default: { // two wheels joined by a long path, to get long thin super-vertices
        int a = ri(g, 3, max(3, maxn / 4)), p = ri(g, 1, max(1, maxn / 3));
        int n = 2 * (a + 1) + p;
        for (int v = 1; v <= a; v++) { E.push_back({0, v}); E.push_back({v, v == a ? 1 : v + 1}); }
        int o = a + 1;
        for (int v = 1; v <= a; v++) { E.push_back({o, o + v}); E.push_back({o + v, v == a ? o + 1 : o + v + 1}); }
        int last = 1;
        for (int i = 0; i < p; i++) { E.push_back({last, 2 * (a + 1) + i}); last = 2 * (a + 1) + i; }
        E.push_back({last, o + 1});
        return dedup(n, E);
    }
    }
}

// ---------- weights ----------
static vector<int> bfs_from(const Net& N, const vector<int>& src, vector<int>* owner = nullptr) {
    vector<vector<int>> a(N.n);
    for (auto& e : N.e) { a[e.first].push_back(e.second); a[e.second].push_back(e.first); }
    vector<int> d(N.n, -1);
    if (owner) owner->assign(N.n, -1);
    vector<int> q;
    for (int s : src) { d[s] = 0; q.push_back(s); if (owner) (*owner)[s] = s; }
    for (size_t i = 0; i < q.size(); i++) for (int y : a[q[i]]) if (d[y] < 0) { d[y] = d[q[i]] + 1; if (owner) (*owner)[y] = (*owner)[q[i]]; q.push_back(y); }
    return d;
}

static Inst make(const Net& N, RNG& g, Stats& st) {
    Inst I; I.n = N.n; I.edges = N.e;
    int wm = ri(g, 0, 10);
    double pboth = (g() % 5) * 0.25;      // both directions
    double pnone = (g() % 3 == 0) ? (g() % 3) * 0.15 : 0.0;     // network edge without arcs
    double ppar = (g() % 4 == 0) ? 0.15 : 0.0;   // parallel arcs
    I.r = ri(g, 0, N.n - 1);
    int centres = ri(g, 1, min(N.n, 8));
    vector<int> cs; for (int i = 0; i < centres; i++) cs.push_back(ri(g, 0, N.n - 1));
    vector<int> owner;
    vector<int> dist = bfs_from(N, cs, &owner);
    int maxw = 1 + (int)(g() % 6);
    auto weight = [&](int a, int b) -> ll {
        switch (wm) {
        case 0: return 0;
        case 1: return ri(g, 0, 1);
        case 2: return ri(g, 0, 2);
        case 3: return ri(g, 0, 9);
        case 4: return ri(g, 0, 1000000);
        case 5: return ri(g, -5, 5);
        case 6: return ri(g, -100000, 100000);
        case 7: // radial: towards the centres cheap, away dear
            if (dist[b] < dist[a]) return ri(g, 0, 2);
            if (dist[b] > dist[a]) return ri(g, 3, 20) + dist[b];
            return ri(g, 1, 6);
        case 8: // zero tree out of the centres, 2-cycles at the centres, random back arcs: A strictly between cycle and K
            if (owner[a] == owner[b]) {
                if (dist[b] == dist[a] + 1) return 0;
                if (dist[a] == dist[b] + 1 && dist[b] == 0 && (g() % 2)) return 0;
                return ri(g, 0, maxw * 2);
            }
            return ri(g, 0, 3 * maxw) + (dist[a] + dist[b]) / 2;
        case 9: // as 8, but dear between regions, and negative shift
            if (owner[a] == owner[b]) {
                if (dist[b] == dist[a] + 1) return -7;
                if (dist[a] == dist[b] + 1 && dist[b] == 0) return -7;
                return -7 + ri(g, 1, maxw);
            }
            return ri(g, 2, 30);
        default: // powers: wide gaps
            return 1LL << ri(g, 0, 20);
        }
    };
    for (auto& e : N.e) {
        int a = e.first, b = e.second;
        double u = (g() % 100000) / 100000.0;
        if (u < pnone) { st.add("n.edges_without_arc"); continue; }
        u = (g() % 100000) / 100000.0;
        if (u < pboth) { I.arcs.push_back({a, b, weight(a, b)}); I.arcs.push_back({b, a, weight(b, a)}); }
        else if (g() & 1) I.arcs.push_back({a, b, weight(a, b)});
        else I.arcs.push_back({b, a, weight(b, a)});
        if ((g() % 100000) / 100000.0 < ppar) { I.arcs.push_back({a, b, weight(a, b)}); st.add("n.parallel_arcs"); }
    }
    // in-arcs of r: sometimes very negative, they must not matter
    if (g() % 3 == 0) for (auto& ar : I.arcs) if (ar.v == I.r) ar.w = -(ll)ri(g, 0, 1000);
    return I;
}

// Pairs on a spanning tree of a planar network: Kruskal order by levels, so that many steps are needed. Non-tree arcs dear.
static Inst hier(const Net& N, RNG& g) {
    Inst I; I.n = N.n; I.edges = N.e;
    vector<int> dsu(N.n); iota(dsu.begin(), dsu.end(), 0);
    function<int(int)> f = [&](int x) { return dsu[x] == x ? x : dsu[x] = f(dsu[x]); };
    vector<pair<int,int>> E = N.e;
    int level = 0;
    vector<char> used(E.size(), 0);
    map<pair<int,int>, int> lev;
    while (true) {
        // a matching on the current components
        shuffle(E.begin(), E.end(), g);
        set<int> touched;
        bool any = false;
        vector<pair<int,int>> merged;
        for (auto& e : E) {
            int a = f(e.first), b = f(e.second);
            if (a != b && !touched.count(a) && !touched.count(b)) { touched.insert(a); touched.insert(b); merged.push_back(e); any = true; }
        }
        for (auto& e : merged) { dsu[f(e.first)] = f(e.second); lev[e] = level; }
        if (!any) break;
        level++;
    }
    ll top = 1;
    for (int i = 0; i < level + 2 && i < 18; i++) top *= 4;
    for (auto& e : N.e) {
        auto it = lev.find(e);
        if (it != lev.end()) {
            ll c = 1; for (int i = 0; i < it->second && i < 18; i++) c *= 4;
            I.arcs.push_back({e.first, e.second, c + ri(g, 0, 1)});
            I.arcs.push_back({e.second, e.first, c + ri(g, 0, 1)});
        } else if (g() % 2) {
            I.arcs.push_back({e.first, e.second, top + ri(g, 0, 9)});
            I.arcs.push_back({e.second, e.first, top + ri(g, 0, 9)});
        }
    }
    I.r = ri(g, 0, N.n - 1);
    return I;
}

// ---------- Corollary 2 ----------
static Inst to_rooted(const Inst& B, ll& M) {
    Inst I = B;
    M = LLONG_MIN;
    for (auto& a : B.arcs) M = max(M, a.w);
    if (B.arcs.empty()) M = 0;
    I.arcs.clear();
    for (auto& a : B.arcs) I.arcs.push_back({a.u, a.v, M - a.w});
    for (int v = 0; v < B.n; v++) I.arcs.push_back({B.n, v, M});
    I.r = B.n;
    return I;
}
static ll brute_branching(const Inst& B, ll limit) {
    vector<vector<int>> in(B.n);
    for (int i = 0; i < (int)B.arcs.size(); i++) in[B.arcs[i].v].push_back(i);
    double prod = 1;
    for (int v = 0; v < B.n; v++) prod *= in[v].size() + 1;
    if (prod > (double)limit) return LLONG_MIN;
    vector<int> par(B.n, -1);
    ll best = LLONG_MIN;
    vector<int> st(B.n, 0); int stamp = 0;
    function<void(int, ll)> rec = [&](int v, ll c) {
        if (v == B.n) {
            for (int s = 0; s < B.n; s++) { stamp++; int x = s; while (x != -1) { if (st[x] == stamp) return; st[x] = stamp; x = par[x]; } }
            best = max(best, c);
            return;
        }
        par[v] = -1; rec(v + 1, c);
        for (int e : in[v]) { par[v] = B.arcs[e].u; rec(v + 1, c + B.arcs[e].w); }
        par[v] = -1;
    };
    rec(0, 0);
    return best;
}

static void print(const Stats& st) {
    printf("{");
    bool first = true;
    for (auto& kv : st.c) { printf("%s\"%s\": %lld", first ? "" : ", ", kv.first.c_str(), kv.second); first = false; }
    printf("}\n");
    fflush(stdout);
}

static double now() { return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count(); }

// ---------- modes ----------
static void exhaustive(RNG& g, int from, int to) {
    struct Case { string name; int n; vector<pair<int,int>> e; vector<ll> alpha; vector<int> roots; };
    const ll X = LLONG_MAX;  // absent
    vector<pair<int,int>> K4 = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
    vector<pair<int,int>> W4 = {{0,1},{0,2},{0,3},{0,4},{1,2},{2,3},{3,4},{4,1}};
    vector<pair<int,int>> K23 = {{0,2},{0,3},{0,4},{1,2},{1,3},{1,4}};
    vector<pair<int,int>> C5 = {{0,1},{1,2},{2,3},{3,4},{4,0}};
    vector<pair<int,int>> C4 = {{0,1},{1,2},{2,3},{3,0}};
    vector<pair<int,int>> C3 = {{0,1},{1,2},{2,0}};
    vector<pair<int,int>> P3 = {{0,1},{1,2}};
    vector<pair<int,int>> P5 = {{0,1},{1,2},{2,3},{3,4}};
    vector<pair<int,int>> K5e = {{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{2,3},{2,4}};   // K5 minus {3,4}: planar
    vector<Case> cs = {
        {"P3", 3, P3, {X, -1, 0, 1, 2, 3}, {0, 1}},
        {"C3", 3, C3, {X, -1, 0, 1, 2, 3}, {0}},
        {"P5", 5, P5, {X, 0, 1, 2, 3}, {0, 1, 2}},
        {"C4", 4, C4, {X, 0, 1, 2, 3}, {0}},
        {"C5", 5, C5, {X, 0, 1, 2}, {0}},
        {"K4", 4, K4, {0, 1, 2}, {0}},
        {"K4x", 4, K4, {X, 0, 1}, {0}},
        {"K23", 5, K23, {0, 1, 2}, {0, 2}},
        {"K23x", 5, K23, {X, 0, 1}, {0, 2}},
        {"W4", 5, W4, {0, 1}, {0, 1}},
        {"W4x", 5, W4, {X, 0}, {0, 1}},
        {"K5e", 5, K5e, {0, 1}, {0, 3}},
        {"K4xx", 4, K4, {X, 0, 1, 2}, {0}},
        {"C6xx", 6, {{0,1},{1,2},{2,3},{3,4},{4,5},{5,0}}, {X, 0, 1, 2}, {0}},
        {"Prism", 6, {{0,1},{1,2},{2,0},{3,4},{4,5},{5,3},{0,3},{1,4},{2,5}}, {0, 1}, {0}},
        {"W5", 6, {{0,1},{0,2},{0,3},{0,4},{0,5},{1,2},{2,3},{3,4},{4,5},{5,1}}, {0, 1}, {0, 1}},
        {"Octa", 6, {{0,1},{0,2},{0,3},{0,4},{5,1},{5,2},{5,3},{5,4},{1,2},{2,3},{3,4},{4,1}}, {0, 1}, {0}},
        {"W4_012", 5, W4, {0, 1, 2}, {0, 1}},
    };
    Stats tot;
    for (int ci = from; ci < (int)cs.size() && ci < to; ci++) {
        auto& c = cs[ci];
        int arcs = 2 * (int)c.e.size();
        ll count = 1; for (int i = 0; i < arcs; i++) count *= (ll)c.alpha.size();
        Stats st;
        double t0 = now();
        for (int root : c.roots) for (ll code = 0; code < count; code++) {
            Inst I; I.n = c.n; I.edges = c.e; I.r = root;
            ll x = code;
            for (int i = 0; i < arcs; i++) {
                ll w = c.alpha[x % (ll)c.alpha.size()]; x /= (ll)c.alpha.size();
                if (w == X) continue;
                auto& ed = c.e[i / 2];
                if (i & 1) I.arcs.push_back({ed.second, ed.first, w}); else I.arcs.push_back({ed.first, ed.second, w});
            }
            Result R = solve(I, g, st, OK, false, true);
            check(I, R, st, false, 2000000, c.name.c_str(), st.c.count("runs") == 0 || st.c.size() < 60);
        }
        printf("%s arcs=%d alphabet=%zu roots=%zu secs=%.1f ", c.name.c_str(), arcs, c.alpha.size(), c.roots.size(), now() - t0);
        print(st);
    }
}

static void random_lane(RNG& g, double secs, int maxn) {
    Stats st;
    double end = now() + secs;
    int heavyN = 150;
    while (now() < end) {
        Net N = network(g, maxn);
        if (N.n < 2) continue;
        Inst I;
        if (g() % 5 == 0) I = hier(N, g); else I = make(N, g, st);
        Result R = solve(I, g, st, OK, false, N.n <= heavyN);
        check(I, R, st, false, N.n <= 9 ? 300000 : 0, "rnd", true);
    }
    print(st);
}

static void corollary_lane(RNG& g, double secs, int maxn) {
    Stats st;
    double end = now() + secs;
    while (now() < end) {
        Net N = network(g, maxn);
        if (N.n < 2) continue;
        Inst B = make(N, g, st);
        // B may be disconnected as a digraph, and may have no arc into a vertex. r is meaningless here.
        ll M;
        Inst I = to_rooted(B, M);
        if (M < 0) st.add("n.all_negative");
        Result R = solve(I, g, st, OK, true, N.n <= 150);
        if (!check(I, R, st, true, N.n <= 7 ? 300000 : 0, "cor", true)) continue;
        // weight of the branching against nM - w(B)
        ll wB = 0; int nb = 0;
        for (int v = 0; v < B.n; v++) { int e = R.inarc[v]; if (I.arcs[e].u != B.n) { wB += B.arcs[e].w; nb++; } }
        if ((ll)B.n * M - R.total != wB) { st.add("FAIL.cor_formula"); printf("FAIL cor formula\n"); }
        st.add("n.branching_arcs", nb);
        if (N.n <= 7) {
            ll bb = brute_branching(B, 3000000);
            if (bb != LLONG_MIN) { st.add("chk.brute_branching"); if (bb != wB) { st.add("FAIL.cor_brute"); printf("FAIL cor brute\n"); } }
        }
    }
    print(st);
}

static void controls(RNG& g0, double secs) {
    vector<pair<string, Ctl>> cs = {{"none", OK}, {"strict(A: d<beta)", STRICT}, {"nosecond(K0*K0*w+1)", NOSECOND}, {"smallK(K0=2)", SMALLK}, {"nodist", NODIST}, {"nobeta", NOBETA}, {"nopath", NOPATH}, {"cycleonly", CYCLEONLY}, {"wholeK", WHOLE}};
    for (auto& c : cs) {
        RNG g(g0());
        Stats st;
        double end = now() + secs;
        ll bad = 0, runs = 0; map<string, ll> why;
        while (now() < end) {
            Net N = network(g, 60);
            if (N.n < 2) continue;
            Inst I = make(N, g, st);
            Result R = solve(I, g, st, c.second, false, false);
            Stats s2;
            runs++;
            if (!check(I, R, s2, false, 0, "ctl", false)) { bad++; for (auto& kv : s2.c) if (kv.first.rfind("FAIL", 0) == 0) why[kv.first] += kv.second; }
        }
        printf("%s: runs=%lld failing=%lld ", c.first.c_str(), runs, bad);
        vector<pair<ll,string>> w2; for (auto& kv : why) w2.push_back({kv.second, kv.first});
        sort(w2.rbegin(), w2.rend());
        for (int i = 0; i < (int)w2.size() && i < 4; i++) printf("[%s %lld] ", w2[i].second.c_str(), w2[i].first);
        printf("\n"); fflush(stdout);
    }
}

static void families(RNG& g) {
    // pairs on a path; hier on a grid; odd n; rho variant with the same pairs
    for (int k : {4, 6, 8, 10, 12}) {
        int n = 1 << k;
        Inst I; I.n = n; I.r = n - 1;
        for (int lev = 0; lev < k; lev++) {
            int step = 1 << lev;
            for (int i = step - 1; i < n - 1; i += 2 * step) {
                I.edges.push_back({i, i + 1});
                ll c = 1LL << (2 * lev);
                I.arcs.push_back({i, i + 1, c + ri(g, 0, 1)});
                I.arcs.push_back({i + 1, i, c + ri(g, 0, 1)});
            }
        }
        Stats st;
        Result R = solve(I, g, st, OK, false, n <= 300);
        bool ok = check(I, R, st, false, 0, "pairs", true);
        printf("pairs n=%d steps=%d calls=%d floorlog2(n-1)=%d ok=%d\n", n, R.steps, R.calls, (int)floor(log2(n - 1)), ok); fflush(stdout);
    }
    for (int a : {4, 8, 16, 32, 45}) {
        vector<pair<int,int>> E;
        for (int i = 0; i < a; i++) for (int j = 0; j < a; j++) { int x = i * a + j; if (j + 1 < a) E.push_back({x, x + 1}); if (i + 1 < a) E.push_back({x, x + a}); }
        Net N = dedup(a * a, E);
        int best = 0; bool allok = true;
        for (int t = 0; t < 8; t++) {
            Inst I = hier(N, g);
            Stats st;
            Result R = solve(I, g, st, OK, false, a <= 12);
            allok &= check(I, R, st, false, 0, "hier-grid", true);
            best = max(best, R.steps);
        }
        printf("hier-grid n=%d best_steps=%d floorlog2(n-1)=%d ok=%d\n", a * a, best, (int)floor(log2(a * a - 1)), allok); fflush(stdout);
    }
}

int main(int argc, char** argv) {
    string mode = argv[1];
    RNG g(argc > 2 ? strtoull(argv[2], nullptr, 10) : 1);
    if (mode == "exh") exhaustive(g, argc > 3 ? atoi(argv[3]) : 0, argc > 4 ? atoi(argv[4]) : 99);
    else if (mode == "rnd") random_lane(g, atof(argv[3]), atoi(argv[4]));
    else if (mode == "cor") corollary_lane(g, atof(argv[3]), atoi(argv[4]));
    else if (mode == "ctl") controls(g, atof(argv[3]));
    else if (mode == "fam") families(g);
    else if (mode == "dump") {
        int cnt = atoi(argv[3]);
        for (int i = 0; i < cnt; i++) { Net N = network(g, 60); printf("%d", N.n); for (auto& e : N.e) printf(" %d %d", e.first, e.second); printf("\n"); }
    }
    return 0;
}
