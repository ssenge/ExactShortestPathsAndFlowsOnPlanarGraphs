// Stress test for notes/DMST.md. Written from the note alone, without reading sim/dmst/dmst.py.
// It runs Sections 4 and 5 on the physical network: one Dijkstra per call of (O), on the
// weights of Section 5, floor decoding, tight pointers, names, and unpacking along stored
// pointers. All free choices of the note (ties, the left-out arc, the arc of beta, the tight
// arc) go through a Chooser, so they are random or enumerated.
// Truth: brute force over in-arc choices, and a standard Chu-Liu/Edmonds. Neither shares code
// with the algorithm.
#include <algorithm>
#include <array>
#include <cmath>
#include <memory>
#include <cassert>
#include <chrono>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
typedef long long ll;
static const ll INFV = LLONG_MAX / 4;

struct Arc { int u, v; ll w; };
struct Net {
  string label; int n = 0; vector<pair<int,int>> E;
  vector<vector<array<int,3>>> adj; // neighbour, edge id, dir (0: first->second as seen from this end)
  void build() {
    adj.assign(n, {});
    for (int e = 0; e < (int)E.size(); e++) {
      adj[E[e].first].push_back({E[e].second, e, 0});
      adj[E[e].second].push_back({E[e].first, e, 1});
    }
  }
  int edgeDir(int u, int v, int &dir) const {
    for (auto &t : adj[u]) if (t[0] == v) { dir = t[2]; return t[1]; }
    return -1;
  }
};
struct Inst { const Net *G = nullptr; vector<Arc> A; int r = 0; bool cor = false; };

// ---------------------------------------------------------------- truth
static ll chuliu(int n, int root, vector<Arc> es) {
  ll res = 0;
  while (true) {
    vector<ll> in(n, INFV); vector<int> pre(n, -1);
    for (auto &e : es) if (e.u != e.v && e.w < in[e.v]) { in[e.v] = e.w; pre[e.v] = e.u; }
    for (int i = 0; i < n; i++) if (i != root && in[i] == INFV) return INFV;
    int cnt = 0; vector<int> id(n, -1), vis(n, -1);
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
    vector<Arc> nx;
    for (auto &e : es) {
      int a = id[e.u], b = id[e.v];
      if (a != b) nx.push_back({a, b, e.w - in[e.v]});
    }
    es.swap(nx);
    n = cnt; root = id[root];
  }
  return res;
}
static vector<char> reachSet(int n, int r, const vector<Arc> &A) {
  vector<char> seen(n, 0); vector<vector<int>> o(n);
  for (auto &a : A) o[a.u].push_back(a.v);
  vector<int> st{r}; seen[r] = 1;
  while (!st.empty()) { int x = st.back(); st.pop_back(); for (int y : o[x]) if (!seen[y]) { seen[y] = 1; st.push_back(y); } }
  return seen;
}
// exhaustive over in-arc choices; returns INFV if over the cap (with *over set)
static ll bruteArb(int n, int r, const vector<Arc> &A, const vector<char> &reach, ll cap, bool *over) {
  vector<vector<int>> in(n);
  for (int i = 0; i < (int)A.size(); i++) if (reach[A[i].u] && reach[A[i].v] && A[i].v != r && A[i].u != A[i].v) in[A[i].v].push_back(i);
  vector<int> vs; ll prod = 1;
  for (int v = 0; v < n; v++) if (reach[v] && v != r) { vs.push_back(v); prod *= max<size_t>(1, in[v].size()); if (prod > cap) { *over = true; return INFV; } }
  *over = false;
  vector<int> par(n, -1); ll best = INFV;
  function<void(int,ll)> go = [&](int i, ll cur) {
    if (i == (int)vs.size()) {
      for (int v : vs) { int x = v, c = 0; while (x != r) { x = par[x]; if (++c > n) return; } }
      best = min(best, cur); return;
    }
    int v = vs[i];
    for (int a : in[v]) { par[v] = A[a].u; go(i + 1, cur + A[a].w); }
  };
  go(0, 0);
  return best;
}
static ll bruteBranching(int n, const vector<Arc> &A, ll cap, bool *over) {
  vector<vector<int>> in(n);
  for (int i = 0; i < (int)A.size(); i++) if (A[i].u != A[i].v) in[A[i].v].push_back(i);
  ll prod = 1;
  for (int v = 0; v < n; v++) { prod *= (in[v].size() + 1); if (prod > cap) { *over = true; return -INFV; } }
  *over = false;
  vector<int> par(n, -1); ll best = -INFV;
  function<void(int,ll)> go = [&](int v, ll cur) {
    if (v == n) {
      for (int s = 0; s < n; s++) { int x = s, c = 0; while (par[x] != -1) { x = par[x]; if (++c > n) return; } }
      best = max(best, cur); return;
    }
    par[v] = -1; go(v + 1, cur);
    for (int a : in[v]) { par[v] = A[a].u; go(v + 1, cur + A[a].w); }
    par[v] = -1;
  };
  go(0, 0);
  return best;
}

// ---------------------------------------------------------------- choices
struct Chooser {
  mt19937_64 rng; int mode = 0; // 0 random, 1 odometer
  vector<int> prefix, counts; size_t pos = 0;
  explicit Chooser(ll seed = 1) : rng(seed) {}
  int pick(int k) {
    if (k <= 1) return 0;
    if (mode == 0) return (int)(rng() % (unsigned long long)k);
    if (pos < prefix.size()) { counts[pos] = k; return prefix[pos++]; }
    prefix.push_back(0); counts.push_back(k); pos++; return 0;
  }
  void start() { pos = 0; }
  bool next() {
    prefix.resize(pos); counts.resize(pos);
    while (!prefix.empty()) {
      if (prefix.back() + 1 < counts.back()) { prefix.back()++; pos = 0; return true; }
      prefix.pop_back(); counts.pop_back();
    }
    return false;
  }
};

// ---------------------------------------------------------------- algorithm
enum Mut { NONE = 0, NODIST, NOBETA, CYCLEONLY, WHOLE, STRICT, NOPATH, NOSECOND, INTERNALH, DIRINTERNAL,
  KEEPUNREACHED, UNPACKFWD, WRONGC, EDGEFOREST, SMALLK0, BETAINSIDE, BETANOD, NOUPDKA, OTHERFOREST, NOINTERNAL,
  NEUTRAL_RIN, NEUTRAL_LEQ_ALL, NMUT };
static const char *mutName[] = {"none", "nodist", "nobeta", "cycleonly", "wholecomp", "strict_lt", "nopath", "nosecond",
  "internal_H_weight", "internal_one_way", "keep_unreached", "unpack_forward", "wrong_c", "edge_level_forest", "small_K0",
  "beta_inside_K", "chosen_by_w_only", "no_update_from_K", "forest_of_next_step", "no_internal_edges", "neutral_in_arcs_of_r", "neutral_recheck"};

struct Stats {
  ll runs = 0, runsActive = 0, steps = 0, activeComps = 0, oracleCalls = 0;
  ll maxSteps = 0;
  ll multiActive = 0, partial = 0, infMember = 0, tieMember = 0, sameTailTwo = 0, zeroCycleNonChosen = 0;
  ll edge2cycle = 0, parallel2cycle = 0, lastArcChosen = 0, piTrivial = 0, piArcs = 0, piInternal = 0, piBareEdge = 0, piHeavyEdge = 0;
  ll mutualKK = 0, nest3 = 0, inArcNeg = 0, unreachedIn = 0, smallReach = 0, rhoTrees2 = 0, rhoChosen = 0, rootBranchEmpty = 0;
  ll betaZero = 0, antiparallelInK = 0, seqChecks = 0, lemma3Checks = 0, subtreeChecks = 0, levelChecks = 0, bruteChecks = 0, cycleLeftChecks = 0;
  ll K2toR = 0, tiedBetaArcs = 0, parallelH = 0, svStrongChecks = 0, svNotStrong = 0, dualSteps = 0, forestPaths = 0, forestPaths3 = 0;
  // the per-run values used for hill climbing
  ll r_steps = 0, r_partial = 0, r_inf = 0, r_tie = 0, r_nest = 0, r_pi = 0, r_multi = 0, r_bare = 0, r_last = 0;
  void clearRun() { r_steps = r_partial = r_inf = r_tie = r_nest = r_pi = r_multi = r_bare = r_last = 0; }
};

struct Crash { string code; };
struct Opt {
  Mut mut = NONE; bool strict = true; bool deep = false; // deep: Lemma 3 per step, sequence check, meta distances
  map<string,ll> *inner = nullptr;
};
struct Out { vector<int> T; ll reported = 0; int steps = 0, calls = 0; int rho = -1; ll M = 0; vector<Arc> B; int nreach = 0; };

struct Fail { string code; };
#define CHECK(cond, code) do { if (!(cond)) { if (opt.strict) throw Fail{code}; else { if (opt.inner) (*opt.inner)[code]++; } } } while (0)

struct StepRec {
  vector<int> nameBefore, chosenBefore, ptr, ptrArc, compOf, cName; vector<ll> D, beta, wBefore, d;
  vector<char> inA; vector<int> activeList;
};

static void oracle(const Net &G, const vector<array<ll,2>> &wt, const vector<int> &src, vector<ll> &D, bool reversed, ll cap = INFV) {
  int n = G.n; D.assign(n, INFV);
  for (auto &w : wt) if (w[0] < 0 || w[1] < 0) throw Crash{"negative_weight_to_oracle"};
  typedef pair<ll,int> P; priority_queue<P, vector<P>, greater<P>> pq;
  for (int s : src) { D[s] = 0; pq.push({0, s}); }
  while (!pq.empty()) {
    auto [du, u] = pq.top(); pq.pop();
    if (du != D[u]) continue;
    if (du >= cap) continue; // at or above X the value means infinity, and a real run needs no more of it
    for (auto &t : G.adj[u]) {
      int v = t[0], e = t[1], dirUV = t[2];
      // forward: arc u->v. reversed: use arc v->u, whose direction index is the opposite of dirUV
      ll w = reversed ? wt[e][1 - dirUV] : wt[e][dirUV];
      if (du + w < D[v]) { D[v] = du + w; pq.push({D[v], v}); }
    }
  }
}

// meta-level distances to c in R[K], by Bellman-Ford on names, written separately from the oracle
static vector<ll> metaDist(int size, const vector<int> &sv, const vector<Arc> &B, const vector<char> &live, const vector<int> &wKeyComp, int K, int c) {
  vector<ll> dist(size, INFV); dist[c] = 0;
  for (bool ch = true; ch;) {
    ch = false;
    for (int a = 0; a < (int)B.size(); a++) if (live[a]) {
      int x = B[a].u, y = B[a].v; if (x >= (int)sv.size() || sv[x] < 0 || sv[y] < 0) continue;
      int sx = sv[x], sy = sv[y]; if (sx == sy) continue;
      if (wKeyComp[sx] != K || wKeyComp[sy] != K) continue;
      if (dist[sy] < INFV && dist[sy] + B[a].w < dist[sx]) { dist[sx] = dist[sy] + B[a].w; ch = true; }
    }
  }
  return dist;
}

static ll stateMinArb(int size, int rootName, const vector<int> &sv, const vector<Arc> &B, const vector<char> &live, int rho) {
  vector<int> id(size + 1, -1); int k = 0;
  vector<Arc> es;
  auto nm = [&](int x) { return x == rho ? rho : sv[x]; };
  for (int a = 0; a < (int)B.size(); a++) if (live[a]) {
    int s = nm(B[a].u), t = nm(B[a].v); if (s < 0 || t < 0 || s == t) continue;
    if (id[s] < 0) id[s] = k++; if (id[t] < 0) id[t] = k++;
    es.push_back({id[s], id[t], B[a].w});
  }
  if (id[rootName] < 0) id[rootName] = k++;
  return chuliu(k, id[rootName], es);
}

static Out runAlgo(const Inst &I, Chooser &ch, const Opt &opt, Stats &st) {
  const Net &G = *I.G; int n = G.n; Out out; st.clearRun();
  int rho = I.cor ? n : -1; int root = I.cor ? n : I.r; out.rho = rho;
  vector<Arc> B = I.A; ll M = 0;
  if (I.cor) {
    bool any = false; for (auto &a : B) { M = any ? max(M, a.w) : a.w; any = true; }
    for (auto &a : B) a.w = M - a.w;
    for (int v = 0; v < n; v++) B.push_back({rho, v, M});
  }
  out.M = M;
  int nb = B.size();
  // arcs per network edge and direction
  vector<int> aEdge(nb, -1), aDir(nb, 0);
  vector<array<vector<int>,2>> onEdge(G.E.size());
  for (int a = 0; a < nb; a++) if (B[a].u != rho) {
    int dir; int e = G.edgeDir(B[a].u, B[a].v, dir);
    if (e < 0) throw Crash{"arc_off_network"};
    aEdge[a] = e; aDir[a] = dir; onEdge[e][dir].push_back(a);
  }
  int size = n + (I.cor ? 1 : 0);
  // ---- Step 1: reach
  vector<char> alive(size, 1);
  int calls = 0;
  if (!I.cor) {
    ll X = n + 1; vector<array<ll,2>> wt(G.E.size());
    for (int e = 0; e < (int)G.E.size(); e++) for (int d = 0; d < 2; d++) wt[e][d] = onEdge[e][d].empty() ? X : 1;
    vector<ll> D; oracle(G, wt, {I.r}, D, false); calls++;
    for (int v = 0; v < n; v++) alive[v] = D[v] < X;
  }
  int nreach = 0; for (int v = 0; v < n; v++) nreach += alive[v] ? 1 : 0;
  out.nreach = nreach;
  if (!I.cor && nreach <= 2 && n >= 4) st.smallReach++;
  vector<char> live(nb, 0);
  for (int a = 0; a < nb; a++) {
    bool ta = B[a].u == rho || alive[B[a].u];
    if (B[a].v == root) { if (B[a].w < 0) st.inArcNeg++; }
    if (!ta && alive[B[a].v]) st.unreachedIn++;
    if (opt.mut == KEEPUNREACHED && !ta && alive[B[a].v] && B[a].v != root) { live[a] = 1; continue; }
    if (opt.mut == NEUTRAL_RIN && ta && alive[B[a].v] && B[a].v == root) { live[a] = 1; continue; }
    live[a] = ta && alive[B[a].v] && B[a].v != root && B[a].u != B[a].v;
  }
  vector<int> sv(size, -1);
  for (int v = 0; v < size; v++) if (alive[v]) sv[v] = v;
  if (I.cor) sv[rho] = rho;
  vector<int> chosen(size, -1);
  ll rep = 0;
  {
    vector<ll> mn(size, INFV);
    for (int a = 0; a < nb; a++) if (live[a] && B[a].v != root) mn[B[a].v] = min(mn[B[a].v], B[a].w);
    vector<vector<int>> at(size);
    for (int a = 0; a < nb; a++) if (live[a] && B[a].v != root && B[a].w == mn[B[a].v]) at[B[a].v].push_back(a);
    for (int v = 0; v < size; v++) if (alive[v] && v != root) {
      if (mn[v] == INFV) throw Crash{"no_in_arc"};
      rep += mn[v];
      chosen[v] = at[v][ch.pick(at[v].size())];
    }
    for (int a = 0; a < nb; a++) if (live[a] && B[a].v != root) { B[a].w -= mn[B[a].v]; CHECK(B[a].w >= 0, "step1_neg"); }
  }
  auto tailName = [&](int a) -> int { int x = B[a].u; return x == rho ? rho : sv[x]; };
  vector<ll> residual(nb, 0); for (int a = 0; a < nb; a++) residual[a] = B[a].w; // after Step 1; the singleton duals are the least in-weights
  vector<StepRec> recs;
  vector<int> renames(size, 0);
  ll aPrev = -1;
  int K0 = n + 1; if (opt.mut == SMALLK0) K0 = 2;
  // ---- Steps
  while (true) {
    // weak components by a spanning forest of the chosen arcs. Random order of arcs means a random forest.
    vector<int> names; for (int v = 0; v < size; v++) if (alive[v] && sv[v] == v) names.push_back(v);
    vector<int> uf(size); iota(uf.begin(), uf.end(), 0);
    function<int(int)> fnd = [&](int x) { while (uf[x] != x) x = uf[x] = uf[uf[x]]; return x; };
    vector<int> order = names;
    if (ch.mode == 0) { for (int i = (int)order.size() - 1; i > 0; i--) swap(order[i], order[ch.rng() % (i + 1)]); }
    vector<int> leftOutArcs;
    set<int> usedEdge;
    set<int> rootMarked;
    for (int S : order) if (S != root) {
      int a = chosen[S];
      if (B[a].u == rho) { continue; }
      int t = tailName(a);
      if (t < 0) { continue; } // only under keep_unreached
      if (opt.mut == EDGEFOREST && aEdge[a] >= 0 && usedEdge.count(aEdge[a])) { continue; } // the second arc on a network edge is not seen
      int x = fnd(S), y = fnd(t);
      if (x == y) leftOutArcs.push_back(a); else { uf[x] = y; if (aEdge[a] >= 0) usedEdge.insert(aEdge[a]); }
    }
    vector<int> comp(size, -1);
    for (int S : names) comp[S] = fnd(S);
    rootMarked.insert(comp[root]); // also for rho, which is a singleton among the names
    int rhoTrees = 0;
    for (int S : names) if (S != root) { int a = chosen[S]; if (B[a].u == rho || tailName(a) < 0) { rootMarked.insert(comp[S]); rhoTrees++; } }
    if (I.cor && rhoTrees >= 2) st.rhoTrees2++;
    if (I.cor) st.rhoChosen += rhoTrees;
    // left-out arc per component
    map<int,vector<int>> leftByComp;
    for (int a : leftOutArcs) leftByComp[comp[sv[B[a].v]]].push_back(a);
    vector<int> activeList;
    map<int,int> cOf; // comp -> c name
    set<int> compSet; for (int S : names) compSet.insert(comp[S]);
    vector<char> onCycle(size, 0);
    for (int K : compSet) {
      bool hasLeft = leftByComp.count(K) > 0;
      CHECK(hasLeft == (rootMarked.count(K) == 0), "cycle_test_wrong");
      if (hasLeft && rootMarked.count(K) == 0) {
        CHECK(leftByComp[K].size() == 1, "two_left_out");
        int a = leftByComp[K][0];
        int c = sv[B[a].v];
        // independent truth: walk the tails from c; must return to c
        vector<int> cyc; int x = c; bool closes = false;
        for (int i = 0; i <= (int)names.size(); i++) { cyc.push_back(x); int t = tailName(chosen[x]); x = t; if (x == c) { closes = true; break; } if (x == root || x < 0) break; }
        st.cycleLeftChecks++;
        CHECK(closes, "left_out_not_on_cycle");
        for (int s : cyc) onCycle[s] = closes ? 1 : onCycle[s];
        if (closes && cyc.size() == 2) {
          int a1 = chosen[cyc[0]], a2 = chosen[cyc[1]];
          if (aEdge[a1] == aEdge[a2]) st.edge2cycle++; else st.parallel2cycle++;
        }
        if (ch.mode == 1 && closes) c = cyc[ch.pick(cyc.size())]; // any arc of the cycle can be the left-out one
        if (opt.mut == WRONGC) {
          vector<int> off; for (int S : names) if (comp[S] == K && !onCycle[S]) off.push_back(S);
          if (!off.empty()) c = off[0];
        }
        cOf[K] = c; activeList.push_back(K);
      }
    }
    if (activeList.empty()) break;
    if ((ll)recs.size() > 2 * n + 3) throw Crash{"no_termination"};
    ll a0 = activeList.size();
    if (aPrev >= 0) CHECK(2 * a0 <= aPrev, "halving");
    aPrev = a0;
    st.activeComps += a0;
    if (a0 >= 2) { st.multiActive++; st.r_multi++; }
    // ---- the call of (O)
    calls++;
    vector<char> isActive(size, 0); for (int K : activeList) isActive[K] = 1;
    ll maxw = 0; for (int a = 0; a < nb; a++) if (live[a]) maxw = max(maxw, B[a].w);
    ll XX = (ll)K0 * K0 * ((ll)(n + 2) * (maxw + 1) + 2);
    if (XX > (1LL << 61)) throw Crash{"overflow_guard"};
    vector<array<ll,2>> wt(G.E.size(), array<ll,2>{XX, XX});
    for (int e = 0; e < (int)G.E.size(); e++) {
      int p = G.E[e].first, q = G.E[e].second;
      if (sv[p] >= 0 && sv[p] == sv[q]) {
        if (opt.mut == INTERNALH) {
          for (int d = 0; d < 2; d++) { ll mw = -1; for (int a : onEdge[e][d]) mw = max(mw, (ll)llabs(I.A[a].w)); wt[e][d] = mw < 0 ? 1 : (1 + (ll)K0 * K0 * mw); }
        } else if (opt.mut == DIRINTERNAL) {
          for (int d = 0; d < 2; d++) wt[e][d] = onEdge[e][d].empty() ? XX : 1;
        } else if (opt.mut == NOINTERNAL) { /* stay removed */
        } else wt[e][0] = wt[e][1] = 1;
      } else if (sv[p] >= 0 && sv[q] >= 0) {
        for (int d = 0; d < 2; d++) for (int a : onEdge[e][d]) if (live[a]) {
          int K = comp[sv[p]];
          if (comp[sv[q]] != K || !isActive[K]) continue;
          ll w = (opt.mut == NOSECOND) ? (ll)K0 * K0 * B[a].w : (ll)K0 * (K0 * B[a].w + 1);
          wt[e][d] = min(wt[e][d], w);
        }
      }
    }
    vector<int> src; set<int> cset; for (auto &kv : cOf) cset.insert(kv.second);
    for (int v = 0; v < n; v++) if (sv[v] >= 0 && cset.count(sv[v])) src.push_back(v);
    vector<ll> D; oracle(G, wt, src, D, true, XX);
    vector<ll> d(size, INFV);
    for (int v = 0; v < n; v++) if (sv[v] >= 0 && D[v] < XX) d[v] = D[v] / K0 / K0;
    if (I.cor) d[rho] = INFV;
    // all vertices of a super-vertex agree
    vector<ll> dS(size, -1);
    for (int v = 0; v < n; v++) if (sv[v] >= 0) {
      int S = sv[v]; if (!isActive[comp[S]]) continue;
      if (dS[S] == -1) dS[S] = d[v]; else CHECK(dS[S] == d[v], "decode_disagree");
    }
    // decoded digits are in range
    for (int v = 0; v < n; v++) if (D[v] < XX) {
      ll rem = D[v] / K0 % K0, lo = D[v] % K0; CHECK(rem + lo <= n - 1 || opt.mut != NONE, "digits_out_of_range");
    }
    // independent distances on names
    if (opt.deep) {
      for (int K : activeList) {
        auto md = metaDist(size, sv, B, live, comp, K, cOf[K]);
        for (int S : names) if (comp[S] == K) CHECK(md[S] == dS[S], "decode_vs_meta");
      }
    }
    // tight pointers
    vector<int> ptr(n, -1), ptrArc(n, -3);
    for (int v = 0; v < n; v++) if (D[v] > 0 && D[v] < XX) {
      vector<array<int,2>> cand;
      for (auto &t : G.adj[v]) {
        int u = t[0], e = t[1], dv = t[2];
        if (D[u] >= INFV) continue;
        if (wt[e][dv] + D[u] == D[v]) {
          // arc v->u. Find which arc it is.
          if (sv[v] >= 0 && sv[v] == sv[u]) { cand.push_back({u, -1}); continue; }
          bool any = false;
          for (int a : onEdge[e][dv]) if (live[a]) {
            if (sv[v] < 0 || sv[u] < 0) continue;
            int K = comp[sv[v]];
            if (comp[sv[u]] != K || !isActive[K]) continue;
            ll w = (opt.mut == NOSECOND) ? (ll)K0 * K0 * B[a].w : (ll)K0 * (K0 * B[a].w + 1);
            if (w == wt[e][dv]) { cand.push_back({u, a}); any = true; }
          }
          if (!any) cand.push_back({u, -2});
        }
      }
      if (cand.empty()) throw Crash{"no_tight_arc"};
      auto c = cand[ch.pick(cand.size())];
      ptr[v] = c[0]; ptrArc[v] = c[1];
    }
    // the one-stretch claim for EVERY path of the forest, not only the paths used in unpacking
    if (opt.deep && opt.mut == NONE) {
      for (int v = 0; v < n; v++) if (sv[v] >= 0 && D[v] > 0 && D[v] < XX) {
        set<int> seenS{sv[v]}; int x = v, cur = sv[v], g = 0; ll piw = 0;
        while (D[x] != 0) {
          int u = ptr[x], pa = ptrArc[x];
          if (u < 0 || ++g > n + 2) throw Crash{"forest_walk"};
          CHECK(pa != -2, "forest_path_uses_removed_arc");
          if (pa >= 0) piw += B[pa].w;
          if (sv[u] != cur) { CHECK(!seenS.count(sv[u]), "forest_path_revisits"); seenS.insert(sv[u]); cur = sv[u]; }
          x = u;
        }
        CHECK(piw == d[v], "forest_path_weight");
        st.forestPaths++;
        if (seenS.size() >= 3) st.forestPaths3++;
      }
    }
    // beta
    map<int,ll> beta; map<int,vector<int>> betaArcs;
    for (int K : activeList) beta[K] = INFV;
    for (int a = 0; a < nb; a++) if (live[a]) {
      int y = B[a].v; if (y == root || sv[y] < 0) continue; int K = comp[sv[y]]; if (!isActive[K]) continue;
      int tn = tailName(a);
      bool outside = tn < 0 || tn == rho || comp[tn] != K;
      if (opt.mut == BETAINSIDE) outside = tn != sv[y];
      if (!outside) continue;
      if (d[y] >= INFV) continue;
      ll val = B[a].w + d[y];
      if (val < beta[K]) { beta[K] = val; betaArcs[K].clear(); }
      if (val == beta[K]) betaArcs[K].push_back(a);
    }
    for (int K : activeList) if (beta[K] >= INFV) throw Crash{"beta_infinite"};
    // the set A
    vector<char> inA(n, 0);
    for (int v = 0; v < n; v++) if (sv[v] >= 0 && isActive[comp[sv[v]]]) {
      int K = comp[sv[v]];
      bool in = d[v] <= beta[K];
      if (opt.mut == CYCLEONLY) in = onCycle[sv[v]];
      if (opt.mut == WHOLE) in = true;
      if (opt.mut == STRICT) in = d[v] < beta[K] || d[v] == 0;
      inA[v] = in;
    }
    // Lemma 1(b) and connectivity of A
    map<int,vector<int>> compMembers; vector<int> sizeOf(size, 0);
    for (int S : names) if (isActive[comp[S]]) compMembers[comp[S]].push_back(S);
    for (int v = 0; v < n; v++) if (sv[v] >= 0) sizeOf[sv[v]]++;
    for (int K : activeList) {
      int c = cOf[K];
      CHECK(inA[c], "c_not_in_A");
      for (int S : compMembers[K]) {
        if (inA[S]) {
          int t = tailName(chosen[S]);
          CHECK(t >= 0 && t != rho && comp[t] == K && inA[t], "chosen_tail_not_in_A");
          if (dS[S] >= INFV) { if (!opt.strict && opt.inner) (*opt.inner)["inf_in_A"]++; }
          if (dS[S] == beta[K] && !onCycle[S]) { st.tieMember++; st.r_tie++; }
        } else {
          if (dS[S] >= INFV) { st.infMember++; st.r_inf++; }
          CHECK(!onCycle[S], "cycle_not_in_A");
        }
      }
      // connected, on the network
      static thread_local vector<int> seenStamp; static thread_local int stamp = 0; if ((int)seenStamp.size() < n) { seenStamp.assign(n, 0); stamp = 0; } stamp++;
      vector<int> stack{c}; seenStamp[c] = stamp; int cnt = 1;
      while (!stack.empty()) { int x = stack.back(); stack.pop_back(); for (auto &t : G.adj[x]) { int u = t[0]; if (seenStamp[u] != stamp && inA[u] && sv[u] >= 0 && comp[sv[u]] == K) { seenStamp[u] = stamp; cnt++; stack.push_back(u); } } }
      int total = 0; for (int S : compMembers[K]) total += sizeOf[S] * (inA[S] ? 1 : 0);
      CHECK(cnt == total, "A_disconnected");
      bool part = false; for (int S : compMembers[K]) if (!inA[S]) part = true;
      if (part) { st.partial++; st.r_partial++; }
      if (beta[K] == 0) st.betaZero++;
      if (betaArcs[K].size() >= 2) st.tiedBetaArcs++;
    }
    // coverage: arcs from one outside super-vertex to two members of A; mutual images; antiparallel arcs in K
    {
      map<pair<int,int>,set<int>> seenTail;
      for (int a = 0; a < nb; a++) if (live[a]) {
        int y = B[a].v; if (y == root || sv[y] < 0) continue; int K = comp[sv[y]]; if (!isActive[K] || !inA[y]) continue;
        int tn = tailName(a); if (tn < 0 || tn == sv[y]) continue;
        if (tn != rho && inA[tn] && comp[tn] == K) continue;
        seenTail[{K, tn}].insert(sv[y]);
      }
      for (auto &kv : seenTail) if (kv.second.size() >= 2) st.sameTailTwo++;
      for (int e = 0; e < (int)G.E.size(); e++) if (!onEdge[e][0].empty() && !onEdge[e][1].empty()) {
        int p = G.E[e].first, q = G.E[e].second; if (sv[p] < 0 || sv[q] < 0 || sv[p] == sv[q]) continue;
        if (comp[sv[p]] == comp[sv[q]] && isActive[comp[sv[p]]]) st.antiparallelInK++;
      }
      map<int,int> img;
      for (int K : activeList) if (!betaArcs[K].empty()) { int t = tailName(betaArcs[K][0]); img[K] = (t < 0 || t == rho) ? -1 : comp[t]; }
      for (auto &kv : img) if (kv.second >= 0 && img.count(kv.second) && img[kv.second] == kv.first) st.mutualKK++;
      for (auto &kv : img) if (kv.second == -1 || (kv.second >= 0 && rootMarked.count(kv.second))) st.K2toR++;
    }
    // Sequence check of "Several components": contract one at a time on a copy and recompute d, beta.
    vector<ll> seqW; vector<char> seqLive; vector<int> seqSv;
    ll minBefore = 0;
    if (opt.deep) minBefore = stateMinArb(size, root, sv, B, live, rho);
    if (opt.deep && activeList.size() >= 2) {
      vector<Arc> B2 = B; vector<char> live2 = live; vector<int> sv2 = sv; vector<int> comp2 = comp;
      vector<int> ord = activeList;
      for (int i = (int)ord.size() - 1; i > 0; i--) swap(ord[i], ord[ch.rng() % (i + 1)]);
      for (int K : ord) {
        int c = cOf[K];
        auto md = metaDist(size, sv2, B2, live2, comp2, K, c);
        for (int S : names) if (comp[S] == K) CHECK(md[S] == dS[S], "seq_d_changed");
        ll b2 = INFV;
        for (int a = 0; a < nb; a++) if (live2[a]) {
          int y = B2[a].v; if (y == root || sv2[y] < 0 || comp2[sv2[y]] != K) continue;
          int x = B2[a].u; int tn = x == rho ? rho : sv2[x];
          if (tn >= 0 && tn != rho && comp2[tn] == K) continue;
          if (md[sv2[y]] >= INFV) continue;
          b2 = min(b2, B2[a].w + md[sv2[y]]);
        }
        CHECK(b2 == beta[K], "seq_beta_changed");
        vector<char> inA2(size, 0);
        for (int S : names) if (comp[S] == K && md[S] <= b2) inA2[S] = 1;
        for (int a = 0; a < nb; a++) if (live2[a]) {
          int y = B2[a].v; if (y == root || sv2[y] < 0 || comp2[sv2[y]] != K) continue;
          if (!inA2[sv2[y]]) continue;
          int x = B2[a].u; int tn = x == rho ? rho : sv2[x];
          if (tn >= 0 && tn != rho && comp2[tn] == K && inA2[tn]) { live2[a] = 0; continue; }
          B2[a].w += md[sv2[y]] - b2;
        }
        for (int v = 0; v < n; v++) if (sv2[v] >= 0 && comp2[sv2[v]] == K && inA2[sv2[v]]) sv2[v] = c;
      }
      st.seqChecks++;
      seqW.assign(nb, 0); seqLive = live2; for (int x = 0; x < nb; x++) seqW[x] = B2[x].w;
      seqSv = sv2;
    }
    // invariant, not a claim of the note: each super-vertex is strongly connected in H
    if (opt.deep) {
      for (int S : names) if (S != rho) {
        vector<int> mem; for (int v = 0; v < n; v++) if (sv[v] == S) mem.push_back(v);
        if (mem.size() < 2) continue;
        st.svStrongChecks++;
        for (int dirn = 0; dirn < 2; dirn++) {
          vector<char> seen(n, 0); vector<int> stk{S}; seen[S] = 1; int cnt = 1;
          while (!stk.empty()) {
            int x = stk.back(); stk.pop_back();
            for (auto &t : G.adj[x]) { int u = t[0]; if (seen[u] || sv[u] != S) continue;
              int e = t[1], dd = dirn == 0 ? t[2] : 1 - t[2];
              if (!onEdge[e][dd].empty()) { seen[u] = 1; cnt++; stk.push_back(u); } }
          }
          if (cnt != (int)mem.size()) st.svNotStrong++;
        }
      }
    }
    // K is connected on the network, and beta is in range
    for (int K : activeList) {
      CHECK(beta[K] <= (ll)n * max<ll>(maxw, 0), "beta_range");
      if (!opt.deep) continue;
      int s0 = -1, tot = 0; for (int v = 0; v < n; v++) if (sv[v] >= 0 && comp[sv[v]] == K) { tot++; if (s0 < 0) s0 = v; }
      vector<char> seen(n, 0); vector<int> stk{s0}; seen[s0] = 1; int cnt = 1;
      while (!stk.empty()) { int x = stk.back(); stk.pop_back(); for (auto &t : G.adj[x]) { int u = t[0]; if (!seen[u] && sv[u] >= 0 && comp[sv[u]] == K) { seen[u] = 1; cnt++; stk.push_back(u); } } }
      CHECK(cnt == tot, "K_disconnected");
    }
    // record
    StepRec rec; rec.nameBefore = sv; rec.chosenBefore = chosen; rec.ptr = ptr; rec.ptrArc = ptrArc; rec.D = D;
    rec.compOf = comp; rec.inA = inA; rec.activeList = activeList; rec.d = d;
    rec.cName.assign(size, -1); for (auto &kv : cOf) rec.cName[kv.first] = kv.second;
    rec.beta.assign(size, 0); for (auto &kv : beta) rec.beta[kv.first] = kv.second;
    rec.wBefore.resize(nb); for (int a = 0; a < nb; a++) rec.wBefore[a] = B[a].w;
    // LP dual: sets A_t = {S in K : d(S) <= t}, t in [0, beta), each of value one per unit of t. Their total is beta.
    // The load of an arc is the measure of t with its head in A_t and its tail not. It must fit in the weight.
    if (opt.mut == NONE) {
      for (int a = 0; a < nb; a++) if (live[a]) {
        int y = B[a].v; if (y == root || sv[y] < 0) continue; int K = comp[sv[y]]; if (!isActive[K]) continue;
        if (d[y] >= INFV || d[y] >= beta[K]) continue;
        int x = B[a].u; ll top = beta[K];
        if (x != rho && sv[x] >= 0 && comp[sv[x]] == K) top = min(top, d[x]);
        if (top > d[y]) residual[a] -= top - d[y];
        CHECK(residual[a] >= 0, "dual_infeasible");
      }
      st.dualSteps++;
    }
    // new chosen arcs, then weights
    map<int,int> newChosen;
    for (int K : activeList) {
      auto &v = betaArcs[K];
      if (v.empty()) throw Crash{"no_beta_arc"};
      newChosen[K] = v[ch.pick(v.size())];
      if (opt.mut == BETANOD) { // the arc of least w into A, instead of least w + d
        int bestA = -1;
        for (int a = 0; a < nb; a++) if (live[a]) { int y = B[a].v; if (y == root || sv[y] < 0 || comp[sv[y]] != K || !inA[y]) continue; int tn = tailName(a); if (tn >= 0 && tn != rho && comp[tn] == K) continue; if (bestA < 0 || B[a].w < B[bestA].w) bestA = a; }
        if (bestA >= 0) newChosen[K] = bestA;
      }
    }
    ll dsum = 0;
    vector<char> vanish(nb, 0);
    for (int a = 0; a < nb; a++) if (live[a]) {
      int y = B[a].v; if (y == root || sv[y] < 0) continue; int K = comp[sv[y]]; if (!isActive[K] || !inA[y]) continue;
      int x = B[a].u;
      bool xIn = x != rho && sv[x] >= 0 && comp[sv[x]] == K && inA[x];
      if (xIn) { vanish[a] = 1; continue; }
      if (opt.mut == NOUPDKA && x != rho && sv[x] >= 0 && comp[sv[x]] == K) continue;
      if (d[y] >= INFV) throw Crash{"inf_in_A_arc"};
      ll nw;
      if (opt.mut == NODIST) nw = B[a].w - beta[K];
      else if (opt.mut == NOBETA) nw = B[a].w + d[y];
      else nw = B[a].w + d[y] - beta[K];
      CHECK(nw >= 0, "L1a_negative");
      CHECK(nw <= B[a].w, "L1a_grew");
      B[a].w = nw;
    }
    for (int a = 0; a < nb; a++) if (vanish[a]) live[a] = 0;
    for (int v = 0; v < n; v++) if (inA[v]) { int K = comp[sv[v]]; sv[v] = -2; renames[v]++; (void)K; }
    {
      vector<int> nmv = rec.nameBefore;
      for (int v = 0; v < n; v++) if (sv[v] == -2) { sv[v] = rec.cName[comp[nmv[v]]]; }
    }
    for (auto &kv : newChosen) chosen[cOf[kv.first]] = kv.second;
    for (auto &kv : beta) { rep += kv.second; dsum += kv.second; }
    // the state is a state
    for (int v = 0; v < size; v++) if (alive[v] && sv[v] == v && v != root) {
      int a = chosen[v]; CHECK(live[a], "chosen_dead"); CHECK(B[a].w == 0, "chosen_not_zero");
      CHECK(sv[B[a].v] == v, "chosen_wrong_head"); CHECK(tailName(a) != v, "chosen_self_loop");
    }
    if (opt.mut == NONE) for (int a = 0; a < nb; a++) if (live[a]) CHECK(residual[a] == B[a].w, "residual_vs_weight");
    if (!seqW.empty()) {
      for (int a = 0; a < nb; a++) { CHECK(seqLive[a] == live[a], "seq_live_differs"); if (live[a]) CHECK(seqW[a] == B[a].w, "seq_weight_differs"); }
      for (int v = 0; v < n; v++) CHECK(seqSv[v] == sv[v], "seq_partition_differs");
    }
    if (opt.deep) {
      ll minAfter = stateMinArb(size, root, sv, B, live, rho);
      st.lemma3Checks++;
      CHECK(minBefore - dsum == minAfter, "lemma3_min_falls_by_beta");
    }
    recs.push_back(std::move(rec));
    st.steps++; st.r_steps++;
    // the bound on calls
    int bound = I.cor ? (n <= 0 ? 0 : 31 - __builtin_clz(max(1, n))) : (nreach <= 1 ? 0 : 31 - __builtin_clz(max(1, nreach - 1)));
    CHECK((int)recs.size() <= bound, "steps_over_bound");
  }
  out.steps = recs.size(); out.calls = calls;
  st.maxSteps = max<ll>(st.maxSteps, recs.size());
  st.oracleCalls += calls;
  // calls <= log2 n + 1
  { double lim = log2((double)max(1, n)) + 1 + 1e-9; if (!I.cor) CHECK((double)calls <= lim, "calls_over_bound"); }
  if (!recs.empty()) st.runsActive++;
  { int mx = 0; for (int v = 0; v < n; v++) mx = max(mx, renames[v]); st.r_nest = mx; if (mx >= 3) st.nest3++; }
  // ---- End and unpacking
  vector<int> inArc(size, -1);
  for (int S = 0; S < size; S++) if (alive[S] && sv[S] == S && S != root) inArc[S] = chosen[S];
  ll curW = 0;
  for (int S = 0; S < size; S++) if (inArc[S] >= 0) { curW += B[inArc[S]].w; }
  CHECK(curW == 0, "final_not_zero");
  vector<int> ordr(recs.size()); iota(ordr.begin(), ordr.end(), 0);
  if (opt.mut != UNPACKFWD) reverse(ordr.begin(), ordr.end());
  for (int t : ordr) {
    StepRec &R = recs[t];
    if (opt.mut == OTHERFOREST && t + 1 < (int)recs.size()) { R.ptr = recs[t + 1].ptr; R.ptrArc = recs[t + 1].ptrArc; R.D = recs[t + 1].D; }
    vector<int> next = inArc;
    // subtree sum on the forest, one mark per y: each vertex on a marked path gets a positive sum
    vector<int> marks(n, 0), byD(n); iota(byD.begin(), byD.end(), 0);
    sort(byD.begin(), byD.end(), [&](int a, int b) { return R.D[a] > R.D[b]; });
    vector<int> ys;
    for (int K : R.activeList) {
      int cN = R.cName[K];
      int a = inArc[cN];
      if (a < 0) throw Crash{"no_in_arc_of_A"};
      int y = B[a].v;
      marks[y] += 1; ys.push_back(y);
    }
    for (int v : byD) if (R.ptr[v] >= 0 && marks[v] > 0) marks[R.ptr[v]] += marks[v];
    st.subtreeChecks++;
    for (int v = 0; v < n; v++) CHECK(marks[v] <= 1, "subtree_two_y");
    vector<char> onPath(n, 0);
    map<int,vector<int>> membersA; // K -> members of A
    for (int S = 0; S < size; S++) if (R.nameBefore[S] == S && S != rho && R.compOf[S] >= 0 && R.inA[S]) membersA[R.compOf[S]].push_back(S);
    for (int K : R.activeList) {
      int cN = R.cName[K];
      int a = inArc[cN];
      int y = B[a].v;
      set<int> assigned;
      if (R.nameBefore[y] < 0 || R.compOf[R.nameBefore[y]] != K) { if (opt.strict) throw Fail{"y_outside_K"}; else if (opt.inner) (*opt.inner)["y_outside_K"]++; }
      int v = y; int guard = 0; ll piW = 0; int firstCycleSeen = 0; (void)firstCycleSeen;
      int lastArc = -1;
      while (R.D[v] != 0) {
        onPath[v] = 1;
        if (++guard > n + 2) throw Crash{"forest_has_cycle"};
        int p = R.ptrArc[v], u = R.ptr[v];
        if (u < 0) throw Crash{"no_pointer"};
        CHECK(R.inA[u], "path_leaves_A");
        if (p == -2) { if (opt.strict) throw Fail{"path_uses_removed_arc"}; else if (opt.inner) (*opt.inner)["path_uses_removed_arc"]++; }
        if (p == -1) {
          st.piInternal++;
          int dir; int e = G.edgeDir(v, u, dir);
          if (onEdge[e][0].empty() && onEdge[e][1].empty()) { st.piBareEdge++; st.r_bare++; }
          else { ll mx = 0; for (int dd = 0; dd < 2; dd++) for (int x : onEdge[e][dd]) mx = max(mx, R.wBefore[x]); if (mx >= 1000) st.piHeavyEdge++; }
        }
        if (p >= 0) {
          int later = R.nameBefore[u];
          CHECK(!assigned.count(later), "path_revisits_supervertex");
          assigned.insert(later);
          next[later] = p;
          st.piArcs++; st.r_pi++;
          piW += R.wBefore[p];
          lastArc = p;
        }
        v = u;
      }
      onPath[v] = 1;
      CHECK(!assigned.count(R.nameBefore[y]), "path_returns_to_S_y");
      if (opt.mut != NOPATH) {
        // the d(y) of the path
        if (R.d[y] < INFV) CHECK(piW == R.d[y], "path_weight_not_d");
      }
      if (lastArc >= 0 && R.chosenBefore[cN] == lastArc) { st.lastArcChosen++; st.r_last++; }
      if (lastArc < 0) st.piTrivial++;
      next[R.nameBefore[y]] = a;
      for (int S : membersA[K]) if (S != R.nameBefore[y] && !assigned.count(S)) next[S] = R.chosenBefore[S];
      if (opt.mut == NOPATH) { for (int S : membersA[K]) if (S != R.nameBefore[y]) next[S] = R.chosenBefore[S]; }
    }
    for (int v = 0; v < n; v++) if (R.D[v] < INFV) CHECK((marks[v] > 0) == (onPath[v] != 0), "subtree_vs_walk");
    inArc = next;
    if (opt.mut != UNPACKFWD) {
      // Lemma 2 at this level: an arborescence of the state before the step, of the right weight
      st.levelChecks++;
      const vector<int> &nm = R.nameBefore;
      ll W = 0;
      for (int S = 0; S < size; S++) if (S != root && alive[S] && nm[S] == S) {
        int a = inArc[S];
        if (a < 0) { CHECK(false, "level_no_in_arc"); continue; }
        W += R.wBefore[a];
        CHECK(nm[B[a].v] == S, "level_head_wrong");
        int x = S, g = 0;
        while (x != root && g <= n + 2) { int aa = inArc[x]; if (aa < 0) break; int tl = B[aa].u; x = tl == rho ? rho : nm[tl]; if (x < 0) break; g++; }
        CHECK(x == root, "level_not_arborescence");
      }
      // weight bookkeeping: the weight of this level is that of the next plus the betas
      ll bsum = 0; for (int K : R.activeList) bsum += R.beta[K];
      CHECK(W == curW + bsum, "level_weight");
      curW = W;
    }
  }
  out.T = inArc; out.reported = rep; out.B = B;
  return out;
}

// ---------------------------------------------------------------- verdict
struct Verdict { bool invalidTree = false, wrongTree = false, wrongReport = false, crash = false, inner = false, stepBound = false; string code; };

static Verdict judge(const Inst &I, Chooser &ch, const Opt &opt, Stats &st, ll bruteCap) {
  Verdict V; const Net &G = *I.G; int n = G.n;
  st.runs++;
  Out out;
  try { out = runAlgo(I, ch, opt, st); }
  catch (Crash &c) { V.crash = true; V.code = c.code; return V; }
  catch (Fail &f) { V.inner = true; V.code = f.code; return V; }
  if (!I.cor) {
    auto reach = reachSet(n, I.r, I.A);
    // truth
    vector<int> id(n, -1); int k = 0; for (int v = 0; v < n; v++) if (reach[v]) id[v] = k++;
    vector<Arc> es; for (auto &a : I.A) if (reach[a.u] && reach[a.v] && a.v != I.r && a.u != a.v) es.push_back({id[a.u], id[a.v], a.w});
    ll t1 = chuliu(k, id[I.r], es);
    bool over = true; ll t2 = bruteArb(n, I.r, I.A, reach, bruteCap, &over);
    if (!over) { st.bruteChecks++; if (t1 != t2) { fprintf(stderr, "TRUTH DISAGREES %lld %lld\n", t1, t2); exit(3); } }
    // the tree
    ll wt = 0; bool valid = true;
    for (int v = 0; v < n; v++) if (reach[v] && v != I.r) {
      int a = v < (int)out.T.size() ? out.T[v] : -1;
      if (a < 0 || a >= (int)I.A.size() || I.A[a].v != v || !reach[I.A[a].u]) { valid = false; break; }
      wt += I.A[a].w;
    }
    if (valid) for (int v = 0; v < n; v++) if (reach[v]) { int x = v, g = 0; while (x != I.r && g <= n + 1) { x = I.A[out.T[x]].u; g++; } if (x != I.r) { valid = false; break; } }
    if (!valid) { V.invalidTree = true; V.code = "invalid_tree"; }
    else if (wt != t1) { V.wrongTree = true; V.code = "tree_weight"; }
    if (out.reported != t1) { V.wrongReport = true; if (V.code.empty()) V.code = "reported_weight"; }
  } else {
    // truth for the branching: separate brute force, and Chu-Liu with its own offset
    ll Big = 1; for (auto &a : I.A) Big = max(Big, a.w + 1);
    vector<Arc> es; for (auto &a : I.A) if (a.u != a.v) es.push_back({a.u, a.v, Big - a.w});
    for (int v = 0; v < n; v++) es.push_back({n, v, Big});
    ll cost = chuliu(n + 1, n, es);
    ll t1 = n * Big - cost;
    bool over = true; ll t2 = bruteBranching(n, I.A, bruteCap, &over);
    if (!over) { st.bruteChecks++; if (t1 != t2) { fprintf(stderr, "TRUTH DISAGREES (branching) %lld %lld\n", t1, t2); exit(3); } }
    ll wb = 0; bool valid = true; int roots = 0;
    for (int v = 0; v < n; v++) {
      int a = out.T[v];
      if (a < 0 || a >= (int)out.B.size() || out.B[a].v != v) { valid = false; break; }
      if (a < (int)I.A.size()) wb += I.A[a].w; else roots++;
    }
    if (valid) for (int v = 0; v < n; v++) { int x = v, g = 0; while (x != n && g <= n + 1) { x = out.B[out.T[x]].u; g++; } if (x != n) { valid = false; break; } }
    if (roots == n) st.rootBranchEmpty++;
    if (!valid) { V.invalidTree = true; V.code = "invalid_branching"; }
    else if (wb != t1) { V.wrongTree = true; V.code = "branching_weight"; }
    ll rep = n * out.M - out.reported;
    if (rep != t1) { V.wrongReport = true; if (V.code.empty()) V.code = "reported_branching"; }
  }
  return V;
}

// ---------------------------------------------------------------- pool and instance IO
static vector<Net> loadPool(const string &fn) {
  ifstream f(fn); int N; f >> N; vector<Net> pool(N);
  for (auto &G : pool) {
    int m; f >> G.label >> G.n >> m; G.E.resize(m);
    for (auto &e : G.E) f >> e.first >> e.second;
    G.build();
  }
  return pool;
}
static void dumpInst(ostream &o, const Inst &I, const string &code) {
  o << "FAIL " << code << " n=" << I.G->n << " cor=" << I.cor << " r=" << I.r << "\n E:";
  for (auto &e : I.G->E) o << " " << e.first << "-" << e.second;
  o << "\n A:";
  for (auto &a : I.A) o << " " << a.u << ">" << a.v << ":" << a.w;
  o << "\n";
}
static long failuresDumped = 0;
static bool report(const Inst &I, const Verdict &V) {
  if (!(V.invalidTree || V.wrongTree || V.wrongReport || V.crash || V.inner)) return false;
  if (failuresDumped++ < 20) dumpInst(cout, I, V.code);
  cout.flush();
  return true;
}
static void printStats(const char *tag, const Stats &s, ll fails, double secs) {
  printf("%s runs=%lld active_runs=%lld steps=%lld active_comps=%lld calls=%lld max_steps=%lld FAILS=%lld secs=%.1f\n", tag, s.runs, s.runsActive, s.steps, s.activeComps, s.oracleCalls, s.maxSteps, fails, secs);
  printf(" cov multi_active=%lld partial_K=%lld d_inf_member=%lld d_eq_beta_noncycle=%lld same_tail_two_members=%lld beta0=%lld tied_beta_arcs=%lld\n", s.multiActive, s.partial, s.infMember, s.tieMember, s.sameTailTwo, s.betaZero, s.tiedBetaArcs);
  printf(" cov 2cycle_one_edge=%lld 2cycle_two_edges=%lld antipar_in_K=%lld mutual_K1_K2=%lld K_to_rootcomp=%lld nest>=3=%lld\n", s.edge2cycle, s.parallel2cycle, s.antiparallelInK, s.mutualKK, s.K2toR, s.nest3);
  printf(" cov pi_arcs=%lld pi_internal_hops=%lld hops_on_edge_without_arc=%lld hops_on_heavy_edge=%lld pi_trivial=%lld pi_last_arc_is_chosen_of_c=%lld\n", s.piArcs, s.piInternal, s.piBareEdge, s.piHeavyEdge, s.piTrivial, s.lastArcChosen);
  printf(" cov neg_in_arc_r=%lld arcs_from_unreached=%lld small_reach=%lld rho_trees>=2=%lld rho_chosen=%lld empty_branching=%lld\n", s.inArcNeg, s.unreachedIn, s.smallReach, s.rhoTrees2, s.rhoChosen, s.rootBranchEmpty);
  printf(" checks brute=%lld lemma3=%lld seq=%lld subtree=%lld level=%lld left_out_on_cycle=%lld sv_strong=%lld sv_not_strong=%lld dual_steps=%lld forest_paths=%lld forest_paths_3plus_supervertices=%lld\n", s.bruteChecks, s.lemma3Checks, s.seqChecks, s.subtreeChecks, s.levelChecks, s.cycleLeftChecks, s.svStrongChecks, s.svNotStrong, s.dualSteps, s.forestPaths, s.forestPaths3);
  fflush(stdout);
}

// ---------------------------------------------------------------- generators
struct Gen {
  mt19937_64 rng; explicit Gen(ll s) : rng(s) {}
  ll ri(ll a, ll b) { return a + (ll)(rng() % (unsigned long long)(b - a + 1)); }
  double rf() { return (double)(rng() >> 11) / (double)(1ULL << 53); }
  void weights(const Net &G, vector<Arc> &A, int kind) {
    int n = G.n;
    vector<ll> pot(n); for (auto &p : pot) p = ri(0, 8);
    map<pair<int,int>,ll> sym;
    for (auto &a : A) {
      switch (kind) {
        case 0: a.w = 0; break;
        case 1: a.w = ri(0, 1); break;
        case 2: a.w = ri(0, 3); break;
        case 3: a.w = ri(0, 10); break;
        case 4: a.w = ri(-5, 5); break;
        case 5: a.w = ri(0, (ll)n * n * n + 1); break;
        case 6: a.w = max<ll>(0, pot[a.v] - pot[a.u] + ri(0, 1)); break; // many zero cycles and ties after reduction
        case 7: a.w = (rf() < 0.2) ? ri(1000, 100000) : ri(0, 2); break; // heavy arcs among light ones
        case 8: { auto k = make_pair(min(a.u, a.v), max(a.u, a.v)); if (!sym.count(k)) sym[k] = ri(0, 6); a.w = sym[k]; break; }
        case 9: { int lv = __builtin_ctz((unsigned)(min(a.u, a.v) + 1)); a.w = (1LL << min(lv, 12)) + ri(0, 1); break; }
        case 10: a.w = (a.v % 2 == 0) ? ri(0, 2) : ri(0, 30); break;
        case 11: a.w = -ri(0, 4); break;
        case 12: a.w = (ll)(abs(a.u - a.v)) * ri(0, 2); break;
        default: a.w = ri(-100000, 100000); break;
      }
    }
  }
  void make(const Net &G, vector<Arc> &A, double p, int kind, double par) {
    A.clear();
    for (auto &e : G.E) {
      if (rf() < p) A.push_back({e.first, e.second, 0});
      if (rf() < p) A.push_back({e.second, e.first, 0});
    }
    if (par > 0) { int m = A.size(); for (int i = 0; i < m; i++) if (rf() < par) A.push_back(A[i]); }
    weights(G, A, kind);
    if (rf() < 0.5) shuffle(A.begin(), A.end(), rng);
  }
};

static vector<int> filt(const vector<Net> &pool, int a, int b) { vector<int> o; for (int i = 0; i < (int)pool.size(); i++) if (pool[i].n >= a && pool[i].n <= b) o.push_back(i); return o; }

typedef chrono::steady_clock Clock;
static double since(Clock::time_point t) { return chrono::duration<double>(Clock::now() - t).count(); }

// ---------------------------------------------------------------- lanes
// Exhaustive over all H with weights from a list, on each graph of the pool with n in the range.
// Graphs whose count is over the budget are sampled, and the output says so.
static int laneExh(const vector<Net> &pool, int a, int b, vector<ll> ws, ll budget, ll seed, bool cor, int odoCap, double maxSecs) {
  Stats st; ll fails = 0; auto t0 = Clock::now(); Gen g(seed); Chooser ch(seed * 7 + 1);
  int fullGraphs = 0, sampledGraphs = 0; ll fullInst = 0, sampledInst = 0, tieRuns = 0;
  Opt opt; opt.deep = true;
  for (int gi : filt(pool, a, b)) {
    const Net &G = pool[gi];
    if (since(t0) > maxSecs) { printf("time limit hit at graph %d\n", gi); break; }
    int m2 = 2 * G.E.size(); int base = ws.size() + 1;
    double total = pow((double)base, m2) * (cor ? 1 : G.n);
    bool full = total <= (double)budget;
    (full ? fullGraphs : sampledGraphs)++;
    ll cnt = full ? (ll)(pow((double)base, m2) + 0.5) : budget;
    int rootsEach = cor ? 1 : (full ? G.n : 1);
    for (ll c = 0; c < cnt; c++) {
      if ((c & 1023) == 0 && since(t0) > maxSecs) break;
      Inst I; I.G = &G; I.cor = cor;
      ll x = c;
      for (int k = 0; k < m2; k++) {
        int dig = full ? (int)(x % base) : (int)(g.rng() % base); x /= base;
        if (dig == 0) continue;
        auto &e = G.E[k / 2];
        if (k % 2 == 0) I.A.push_back({e.first, e.second, ws[dig - 1]}); else I.A.push_back({e.second, e.first, ws[dig - 1]});
      }
      for (int rr = 0; rr < rootsEach; rr++) {
        I.r = full ? rr : (int)(g.rng() % G.n);
        if (odoCap <= 1) {
          Verdict V = judge(I, ch, opt, st, 100000);
          if (report(I, V)) fails++;
          (full ? fullInst : sampledInst)++;
        } else {
          Chooser od(seed); od.mode = 1; int runs = 0;
          do {
            od.start();
            Verdict V = judge(I, od, opt, st, runs == 0 ? 100000 : 0);
            if (report(I, V)) fails++;
            tieRuns++;
          } while (++runs < odoCap && od.next());
          (full ? fullInst : sampledInst)++;
        }
      }
    }
  }
  printf("exhaustive lane n in [%d,%d] weights=", a, b); for (ll w : ws) printf("%lld,", w);
  printf(" cor=%d full_graphs=%d sampled_graphs=%d full_instances=%lld sampled_instances=%lld tie_runs=%lld\n", cor, fullGraphs, sampledGraphs, fullInst, sampledInst, tieRuns);
  printStats("EXH", st, fails, since(t0));
  return fails ? 1 : 0;
}

static int laneRnd(const vector<Net> &pool, int a, int b, double secs, ll seed, bool cor, bool deepSmall) {
  Stats st; ll fails = 0; auto t0 = Clock::now(); Gen g(seed); Chooser ch(seed * 13 + 5);
  auto idx = filt(pool, a, b);
  double ps[] = {0.25, 0.4, 0.55, 0.7, 0.85, 1.0};
  long iter = 0;
  while (true) {
    if ((iter++ & 255) == 0 && since(t0) > secs) break;
    const Net &G = pool[idx[g.rng() % idx.size()]];
    Inst I; I.G = &G; I.cor = cor; I.r = g.rng() % G.n;
    g.make(G, I.A, ps[g.rng() % 6], g.rng() % 14, g.rf() < 0.15 ? 0.3 : 0.0);
    Opt opt; opt.deep = deepSmall && G.n <= 24;
    Verdict V = judge(I, ch, opt, st, G.n <= 12 ? 20000 : 0);
    if (report(I, V)) fails++;
  }
  printStats(cor ? "RND-COR" : "RND", st, fails, since(t0));
  return fails ? 1 : 0;
}

// Hill climbing. Objective chosen by name. Each candidate is run under several tie seeds, and the
// score is the best seen.
static ll scoreOf(const Stats &s, int obj) {
  switch (obj) {
    case 0: return s.r_steps;
    case 1: return 1000 * s.r_steps + 40 * s.r_partial + 12 * s.r_inf + 6 * s.r_tie + 25 * s.r_nest + 2 * s.r_pi + 10 * s.r_multi + s.r_bare;
    case 2: return s.r_partial * 10 + s.r_inf;
    case 3: return s.r_nest * 10 + s.r_steps;
    case 4: return s.r_pi;
    case 5: return s.r_bare * 3 + s.r_pi;
    case 6: return s.r_last;
    default: return s.r_steps;
  }
}
static int laneHill(const vector<Net> &pool, int a, int b, double secs, ll seed, bool cor, int obj, int climbLen) {
  Stats st; ll fails = 0; auto t0 = Clock::now(); Gen g(seed); Chooser ch(seed * 17 + 3);
  auto idx = filt(pool, max(a, 2), b);
  ll bestEver = -1; map<int,int> bestStepsByN; map<int,ll> gapHit; long restarts = 0, moves = 0, accepted = 0;
  Inst bestI;
  auto eval = [&](Inst &I, int seeds) -> ll {
    ll best = -1;
    for (int s = 0; s < seeds; s++) {
      Opt opt; opt.deep = I.G->n <= 18;
      Verdict V = judge(I, ch, opt, st, I.G->n <= 10 ? 5000 : 0);
      if (report(I, V)) fails++;
      best = max(best, scoreOf(st, obj));
      int n = I.G->n; bestStepsByN[n] = max<int>(bestStepsByN[n], st.r_steps);
    }
    return best;
  };
  while (since(t0) < secs) {
    restarts++;
    const Net &G = pool[idx[g.rng() % idx.size()]];
    Inst I; I.G = &G; I.cor = cor; I.r = g.rng() % G.n;
    int kind = g.rng() % 14;
    g.make(G, I.A, 0.5 + 0.5 * g.rf(), kind, 0.0);
    ll cur = eval(I, 3);
    for (int it = 0; it < climbLen && since(t0) < secs; it++) {
      moves++;
      Inst J = I;
      int nm = 1 + g.rng() % 3;
      for (int q = 0; q < nm; q++) {
        int mv = g.rng() % 8;
        if (mv <= 3 && !J.A.empty()) { auto &x = J.A[g.rng() % J.A.size()]; ll sc = (ll)1 << (g.rng() % 8); x.w += (g.rng() % 2 ? sc : -sc); if (x.w < -50 || g.rng() % 8 == 0) x.w = g.ri(0, 8); }
        else if (mv == 4 && !J.A.empty()) { auto &x = J.A[g.rng() % J.A.size()]; x.w = 0; }
        else if (mv == 5 && J.A.size() > 1) { int i = g.rng() % J.A.size(); J.A[i] = J.A.back(); J.A.pop_back(); }
        else if (mv == 6) { auto &e = G.E[g.rng() % G.E.size()]; if (g.rng() % 2) J.A.push_back({e.first, e.second, g.ri(0, 8)}); else J.A.push_back({e.second, e.first, g.ri(0, 8)}); }
        else if (mv == 7 && !cor && g.rng() % 8 == 0) J.r = g.rng() % G.n;
      }
      ll sc = eval(J, 2);
      if (sc >= cur) { if (sc > cur) accepted++; I = std::move(J); cur = sc; }
      if (cur > bestEver) { bestEver = cur; bestI = I; }
    }
  }
  printf("hill obj=%d cor=%d restarts=%ld moves=%ld improved=%ld best=%lld\n", obj, cor, restarts, moves, accepted, bestEver);
  printf(" best steps by n:"); for (auto &kv : bestStepsByN) printf(" %d:%d(bound %d)", kv.first, kv.second, cor ? (kv.first > 0 ? 31 - __builtin_clz(kv.first) : 0) : (kv.first > 1 ? 31 - __builtin_clz(kv.first - 1) : 0)); printf("\n");
  if (bestI.G) {
    dumpInst(cout, bestI, "BEST-OF-CLIMB(not a failure)");
    Chooser od(seed); od.mode = 1; ll tr = 0; Opt opt; opt.deep = bestI.G->n <= 18;
    do { od.start(); Verdict V = judge(bestI, od, opt, st, 0); if (report(bestI, V)) fails++; tr++; } while (tr < 3000 && od.next());
    printf(" all-ties runs on the best instance: %lld%s\n", tr, tr >= 3000 ? " (capped)" : " (complete)");
  }
  printStats("HILL", st, fails, since(t0));
  return fails ? 1 : 0;
}

// Hill climbing seeded from a family file, so that it starts at the bound of Lemma 4 and stays near it.
// Moves change weights, drop arcs and add arcs on network edges, so the planar network stays as checked in gen_fam.py.
static int laneHillF(const string &fn, int nmax, double secs, ll seed, int obj, int climbLen, const string &prefix) {
  ifstream f(fn); string word; vector<unique_ptr<Net>> nets; vector<Inst> seeds;
  while (f >> word) {
    auto G = make_unique<Net>(); G->label = word; int m, r, cr; f >> G->n >> m >> r >> cr; G->E.resize(m);
    for (auto &e : G->E) f >> e.first >> e.second;
    G->build();
    int k; f >> k; Inst I; I.A.resize(k); for (auto &a : I.A) f >> a.u >> a.v >> a.w;
    I.r = r; I.cor = cr;
    if (G->n <= nmax && G->n >= 5 && word.rfind(prefix, 0) == 0) { I.G = G.get(); seeds.push_back(I); nets.push_back(std::move(G)); }
  }
  Stats st; ll fails = 0; auto t0 = Clock::now(); Gen g(seed); Chooser ch(seed * 29 + 3);
  long restarts = 0, moves = 0, accepted = 0; map<int,int> bestSteps, startSteps; ll atBound = 0, overBound = 0, partialAtBound = 0, infAtBound = 0;
  auto boundOf = [](const Inst &I) { int n = I.G->n; return I.cor ? 31 - __builtin_clz(max(1, n)) : (n > 1 ? 31 - __builtin_clz(max(1, n - 1)) : 0); };
  auto eval = [&](Inst &I, int nseeds) -> ll {
    ll best = -1;
    for (int s = 0; s < nseeds; s++) {
      Opt opt; opt.deep = I.G->n <= 33;
      Verdict V = judge(I, ch, opt, st, I.G->n <= 10 ? 5000 : 0);
      if (report(I, V)) fails++;
      best = max(best, scoreOf(st, obj));
      int n = I.G->n; bestSteps[n] = max<int>(bestSteps[n], st.r_steps);
      if (st.r_steps == boundOf(I)) { atBound++; partialAtBound += st.r_partial > 0; infAtBound += st.r_inf > 0; }
      if (st.r_steps > boundOf(I)) overBound++;
    }
    return best;
  };
  while (since(t0) < secs) {
    restarts++;
    Inst I = seeds[g.rng() % seeds.size()];
    const Net &G = *I.G;
    ll cur = eval(I, 2);
    for (int it = 0; it < climbLen && since(t0) < secs; it++) {
      moves++;
      Inst J = I;
      int nm = 1 + g.rng() % 3;
      for (int q = 0; q < nm; q++) {
        int mv = g.rng() % 9;
        if (mv <= 2 && !J.A.empty()) { auto &x = J.A[g.rng() % J.A.size()]; ll sc = (ll)1 << (g.rng() % 6); x.w += (g.rng() % 2 ? sc : -sc); }
        else if (mv == 3 && !J.A.empty()) { auto &x = J.A[g.rng() % J.A.size()]; x.w = 0; }
        else if (mv == 4 && !J.A.empty()) { auto &x = J.A[g.rng() % J.A.size()]; auto &y = J.A[g.rng() % J.A.size()]; x.w = y.w; }
        else if (mv == 5 && J.A.size() > 1) { int i = g.rng() % J.A.size(); J.A[i] = J.A.back(); J.A.pop_back(); }
        else if (mv >= 6 && !G.E.empty()) { auto &e = G.E[g.rng() % G.E.size()]; ll w = J.A.empty() ? 1 : J.A[g.rng() % J.A.size()].w + g.ri(-1, 1); if (g.rng() % 2) J.A.push_back({e.first, e.second, w}); else J.A.push_back({e.second, e.first, w}); }
      }
      ll sc = eval(J, 1);
      if (sc >= cur) { if (sc > cur) accepted++; I = std::move(J); cur = sc; }
    }
  }
  printf("hillf prefix=%s nmax=%d obj=%d seeds=%zu restarts=%ld moves=%ld improved=%ld runs_at_bound=%lld with_partial=%lld with_d_inf=%lld over_bound=%lld\n", prefix.c_str(), nmax, obj, seeds.size(), restarts, moves, accepted, atBound, partialAtBound, infAtBound, overBound);
  printf(" best steps by n:"); for (auto &kv : bestSteps) printf(" %d:%d", kv.first, kv.second); printf("\n");
  printStats("HILLF", st, fails, since(t0));
  return fails ? 1 : 0;
}

// Controls: each mutation runs on a fixed stream; the table shows what the final compare (tree and
// weight against the truth) sees, and what the inner checks see. The instance stream is that of the
// random lane restricted to small n, so the rates compare.
static int laneCtl(const vector<Net> &pool, int a, int b, double secsEach, ll seed, bool cor) {
  auto idx = filt(pool, a, b);
  printf("control table cor=%d n in [%d,%d]\n", cor, a, b);
  printf("%-26s %8s %8s %8s %8s %8s %8s  %s\n", "mutation", "runs", "invalid", "wrongT", "wrongR", "crash", "innerAny", "inner codes");
  double ps[] = {0.25, 0.4, 0.55, 0.7, 0.85, 1.0};
  for (int m = 0; m < NMUT; m++) {
    Mut mu = (Mut)m;
    if (mu == KEEPUNREACHED && cor) continue;
    Stats st; Gen g(seed); Chooser ch(seed * 19 + 1); map<string,ll> inner, crashes;
    ll inv = 0, wt = 0, wr = 0, cr = 0, runs = 0, innerRuns = 0; auto t0 = Clock::now(); long iter = 0;
    while (true) {
      if ((iter++ & 63) == 0 && since(t0) > secsEach) break;
      const Net &G = pool[idx[g.rng() % idx.size()]];
      Inst I; I.G = &G; I.cor = cor; I.r = g.rng() % G.n;
      g.make(G, I.A, ps[g.rng() % 6], g.rng() % 14, g.rf() < 0.15 ? 0.3 : 0.0);
      Opt opt; opt.mut = mu; opt.strict = false; opt.inner = &inner; opt.deep = false;
      ll before = 0; for (auto &kv : inner) before += kv.second;
      Verdict V = judge(I, ch, opt, st, 0);
      ll after = 0; for (auto &kv : inner) after += kv.second;
      runs++;
      if (after > before) innerRuns++;
      if (V.invalidTree) inv++;
      if (V.wrongTree) wt++;
      if (V.wrongReport) wr++;
      if (V.crash) { cr++; crashes[V.code]++; }
    }
    string codes; int shown = 0; for (auto &kv : inner) { if (shown++ < 6) codes += kv.first + "=" + to_string(kv.second) + " "; }
    for (auto &kv : crashes) codes += "!" + kv.first + "=" + to_string(kv.second) + " ";
    printf("%-26s %8lld %8lld %8lld %8lld %8lld %8lld  %s\n", mutName[m], runs, inv, wt, wr, cr, innerRuns, codes.c_str());
    fflush(stdout);
  }
  return 0;
}

// One instance from a file: n m r cor, edges, then k arcs. The planarity of the network is checked by
// the Python generator that wrote the file.
static int laneFile(const string &fn, int tieSeeds, bool brute) {
  ifstream f(fn); string word; int count = 0; ll fails = 0; Stats st; auto t0 = Clock::now();
  vector<unique_ptr<Net>> keep;
  while (f >> word) {
    auto G = make_unique<Net>(); G->label = word; int m, r, cr; f >> G->n >> m >> r >> cr; G->E.resize(m);
    for (auto &e : G->E) f >> e.first >> e.second;
    G->build();
    int k; f >> k; Inst I; I.A.resize(k); for (auto &a : I.A) f >> a.u >> a.v >> a.w;
    I.G = G.get(); I.r = r; I.cor = cr;
    Chooser ch(12345 + count);
    int mx = 0; ll localFails = 0; int bound = cr ? 31 - __builtin_clz(max(1, G->n)) : (G->n > 1 ? 31 - __builtin_clz(G->n - 1) : 0);
    for (int s = 0; s < tieSeeds; s++) {
      Opt opt; opt.deep = G->n <= 64;
      Verdict V = judge(I, ch, opt, st, brute ? 100000 : 0);
      if (report(I, V)) { localFails++; fails++; }
      mx = max<int>(mx, st.r_steps);
    }
    printf("%-14s n=%-6d m=%-7d arcs=%-7d steps=%d floor_log2(n-1)=%d fails=%lld\n", G->label.c_str(), G->n, m, k, mx, bound, localFails);
    keep.push_back(std::move(G)); count++;
  }
  printStats("FILE", st, fails, since(t0));
  return fails ? 1 : 0;
}

int main(int argc, char **argv) {
  string mode = argv[1];
  if (mode == "file") return laneFile(argv[2], atoi(argv[3]), atoi(argv[4]));
  if (mode == "hillf") return laneHillF(argv[2], atoi(argv[3]), atof(argv[4]), atoll(argv[5]), atoi(argv[6]), atoi(argv[7]), argv[8]);
  auto pool = loadPool(argv[2]);
  if (mode == "exh") {
    int a = atoi(argv[3]), b = atoi(argv[4]); vector<ll> ws; { stringstream ss(argv[5]); string t; while (getline(ss, t, ',')) ws.push_back(atoll(t.c_str())); }
    return laneExh(pool, a, b, ws, atoll(argv[6]), atoll(argv[7]), atoi(argv[8]), atoi(argv[9]), atof(argv[10]));
  }
  if (mode == "rnd") return laneRnd(pool, atoi(argv[3]), atoi(argv[4]), atof(argv[5]), atoll(argv[6]), atoi(argv[7]), atoi(argv[8]));
  if (mode == "hill") return laneHill(pool, atoi(argv[3]), atoi(argv[4]), atof(argv[5]), atoll(argv[6]), atoi(argv[7]), atoi(argv[8]), atoi(argv[9]));
  if (mode == "ctl") return laneCtl(pool, atoi(argv[3]), atoi(argv[4]), atof(argv[5]), atoll(argv[6]), atoi(argv[7]));
  return 2;
}
