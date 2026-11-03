// Lemma-level stress test for Section 3 of notes/DMST.md. It shares no code with dm.cpp.
// The lemmas are claimed for ANY state: any nonnegative weights, any zero-weight chosen arcs, one
// contraction of one active component, any c on its cycle, any arc attaining beta, any shortest path.
// So this enumerates states directly on the networks of the pool, including states the algorithm
// never reaches. Super-vertices are singletons here; parallel arcs stand for contracted members.
//
// Checks, for every (state, K, c, arc of beta):
//  L1a  0 <= w' <= w, new chosen arc has weight 0
//  L1b  cycle in A, chosen tails of members in A, shortest paths in A, A connected through R[K]
//  L2   for every arborescence T' after the contraction and every simple shortest path pi:
//       the T of Lemma 2 is an arborescence and w(T) = w'(T') + beta
//  L3   for every arborescence T the T' of the proof is an arborescence and w'(T') <= w(T) - beta
//  EQ   min after = min before - beta, by separate brute force on both sides
//  L4   after contracting ALL active components, at most half as many are active
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
typedef long long ll;
static const ll INF = 1LL << 50;
struct Arc { int u, v; ll w; };
struct Graph { string label; int n; vector<pair<int,int>> E; };
static int MUT = 0; // 0 none, 1 strict A, 2 w'=w-beta, 3 A=cycle, 4 unpack ignores pi, 5 beta over w only
static ll nStates = 0, nContr = 0, nT2 = 0, nT3 = 0, nEq = 0, nL4 = 0, fails = 0, nLastChosen = 0, nPi = 0, nInf = 0, nPartial = 0, nTieA = 0;
static map<string,ll> failCodes;
static const Arc *dumpArcs = nullptr; static int dumpN = 0, dumpM = 0;
static void bad(const string &code, int n, int r, const vector<Arc> &A, const vector<int> &chosen, int c) {
  fails++; failCodes[code]++;
  if (MUT == 0 && fails <= 10) {
    printf("FAIL %s n=%d r=%d c=%d\n arcs:", code.c_str(), n, r, c);
    for (auto &a : A) printf(" %d>%d:%lld", a.u, a.v, a.w);
    printf("\n chosen:"); for (int i = 0; i < n; i++) printf(" %d", chosen[i]);
    printf("\n"); fflush(stdout);
  }
}
// all arborescences of (n, arcs) rooted at r, as in-arc vectors
template <class F> static void forArb(int n, int r, const vector<Arc> &A, F f) {
  vector<vector<int>> in(n);
  for (int i = 0; i < (int)A.size(); i++) if (A[i].v != r && A[i].u != A[i].v) in[A[i].v].push_back(i);
  vector<int> par(n, -1), T(n, -1);
  function<void(int)> go = [&](int v) {
    if (v == n) {
      for (int s = 0; s < n; s++) { int x = s, g = 0; while (x != r) { x = par[x]; if (++g > n) return; } }
      f(T); return;
    }
    if (v == r) { go(v + 1); return; }
    for (int a : in[v]) { par[v] = A[a].u; T[v] = a; go(v + 1); }
    par[v] = -1; T[v] = -1;
  };
  go(0);
}
static ll minArb(int n, int r, const vector<Arc> &A) {
  ll best = INF;
  forArb(n, r, A, [&](const vector<int> &T) { ll s = 0; for (int v = 0; v < n; v++) if (v != r) s += A[T[v]].w; best = min(best, s); });
  return best;
}
static void checkState(int n, int r, const vector<Arc> &A, const vector<int> &chosen) {
  nStates++;
  // components of the chosen arcs
  vector<int> comp(n); for (int i = 0; i < n; i++) comp[i] = i;
  function<int(int)> fd = [&](int x) { return comp[x] == x ? x : comp[x] = fd(comp[x]); };
  for (int v = 0; v < n; v++) if (v != r) comp[fd(v)] = fd(A[chosen[v]].u);
  ll minBefore = minArb(n, r, A);
  set<int> actives; for (int v = 0; v < n; v++) if (fd(v) != fd(r)) actives.insert(fd(v));
  for (int K : actives) {
    // the cycle: walk tails from any member
    int s = -1; for (int v = 0; v < n; v++) if (fd(v) == K) { s = v; break; }
    int x = s; for (int i = 0; i < n + 1; i++) x = A[chosen[x]].u;
    vector<int> cyc; { int y = x; do { cyc.push_back(y); y = A[chosen[y]].u; } while (y != x); }
    vector<char> onC(n, 0); for (int y : cyc) onC[y] = 1;
    for (int c : cyc) {
      // d by Bellman-Ford in R[K]
      vector<ll> d(n, INF); d[c] = 0;
      for (int i = 0; i < n; i++) for (auto &a : A) if (fd(a.u) == K && fd(a.v) == K && d[a.v] < INF && d[a.v] + a.w < d[a.u]) d[a.u] = d[a.v] + a.w;
      for (int v = 0; v < n; v++) if (fd(v) == K && d[v] >= INF) nInf++;
      ll beta = INF; vector<int> attain;
      for (int i = 0; i < (int)A.size(); i++) if (fd(A[i].u) != K && fd(A[i].v) == K && A[i].v != r && d[A[i].v] < INF) {
        ll val = MUT == 5 ? A[i].w : A[i].w + d[A[i].v];
        if (val < beta) { beta = val; attain.clear(); }
        if (val == beta) attain.push_back(i);
      }
      if (beta >= INF) { bad("beta_infinite", n, r, A, chosen, c); continue; }
      vector<char> inA(n, 0);
      for (int v = 0; v < n; v++) if (fd(v) == K) {
        inA[v] = d[v] <= beta;
        if (MUT == 1) inA[v] = d[v] < beta || d[v] == 0;
        if (MUT == 3) inA[v] = onC[v];
      }
      bool part = false; for (int v = 0; v < n; v++) if (fd(v) == K && !inA[v]) part = true; if (part) nPartial++;
      for (int v = 0; v < n; v++) if (fd(v) == K && inA[v] && !onC[v] && d[v] == beta) nTieA++;
      // L1b
      for (int y : cyc) if (!inA[y]) bad("L1b_cycle", n, r, A, chosen, c);
      for (int v = 0; v < n; v++) if (inA[v] && !inA[A[chosen[v]].u]) bad("L1b_chosen_tail", n, r, A, chosen, c);
      // shortest paths stay in A: every tight arc from a member of A leads into A
      for (auto &a : A) if (inA[a.u] && fd(a.v) == K && d[a.v] < INF && a.w + d[a.v] == d[a.u] && !inA[a.v] && MUT != 3) bad("L1b_path", n, r, A, chosen, c);
      // contracted graph
      vector<int> id(n, -1); int k = 0; for (int v = 0; v < n; v++) if (!inA[v]) id[v] = k++;
      int aid = k++; for (int v = 0; v < n; v++) if (inA[v]) id[v] = aid;
      vector<Arc> B; vector<int> back; // back: index into A
      for (int i = 0; i < (int)A.size(); i++) {
        auto &a = A[i]; if (inA[a.u] && inA[a.v]) continue;
        ll w = a.w;
        if (inA[a.v]) { w = MUT == 2 ? a.w - beta : a.w + d[a.v] - beta;
          if (w < 0) bad("L1a_neg", n, r, A, chosen, c);
          if (w > a.w) bad("L1a_grew", n, r, A, chosen, c); }
        B.push_back({id[a.u], id[a.v], w}); back.push_back(i);
      }
      nContr++;
      for (int at : attain) { ll w0 = A[at].w + d[A[at].v] - beta; if (w0 != 0 && MUT != 5 && MUT != 2) bad("L1a_chosen", n, r, A, chosen, c); if (!inA[A[at].v]) bad("beta_head_outside_A", n, r, A, chosen, c); }
      // EQ
      ll minAfter = minArb(k, id[r], B); nEq++;
      if (minBefore < INF && minAfter != minBefore - beta) bad("EQ_min_falls_by_beta", n, r, A, chosen, c);
      // all simple shortest paths from each y to c inside K
      map<int,vector<vector<int>>> pathsFrom;
      auto simplePaths = [&](int y) -> vector<vector<int>> & {
        auto it = pathsFrom.find(y); if (it != pathsFrom.end()) return it->second;
        auto &res = pathsFrom[y];
        vector<int> cur; vector<char> seen(n, 0); seen[y] = 1;
        function<void(int,ll)> dfs = [&](int v, ll acc) {
          if (v == c) { if (acc == d[y]) res.push_back(cur); return; }
          for (int i = 0; i < (int)A.size(); i++) if (A[i].u == v && fd(A[i].v) == K && !seen[A[i].v] && acc + A[i].w <= d[y]) {
            seen[A[i].v] = 1; cur.push_back(i); dfs(A[i].v, acc + A[i].w); cur.pop_back(); seen[A[i].v] = 0;
          }
        };
        dfs(y, 0); return res;
      };
      // L2 over all T' and all pi
      forArb(k, id[r], B, [&](const vector<int> &Tp) {
        ll wp = 0; for (int v = 0; v < k; v++) if (v != id[r]) wp += B[Tp[v]].w;
        int ain = back[Tp[aid]]; int y = A[ain].v; // the in-arc of A, in terms of H
        auto &ps = simplePaths(y);
        if (ps.empty() && MUT == 0) bad("L2_no_path", n, r, A, chosen, c);
        for (auto &pi : ps) {
          nT2++; nPi++;
          vector<int> T(n, -1);
          for (int v = 0; v < n; v++) if (!inA[v] && v != r) { int nv = id[v]; T[v] = back[Tp[nv]]; }
          for (int v = 0; v < n; v++) if (inA[v]) T[v] = chosen[v];
          if (MUT != 4) for (int a : pi) T[A[a].v] = a;
          T[y] = ain;
          if (!pi.empty() && pi.back() == chosen[c]) nLastChosen++;
          bool ok = true; ll w = 0;
          for (int v = 0; v < n; v++) if (v != r) { w += A[T[v]].w; int xx = v, g = 0; while (xx != r && g <= n + 1) { xx = A[T[xx]].u; g++; } if (xx != r) ok = false; }
          if (!ok) bad("L2_not_arborescence", n, r, A, chosen, c);
          else if (w != wp + beta) bad("L2_weight", n, r, A, chosen, c);
        }
      });
      // L3 over all T, with the T' of the proof
      forArb(n, r, A, [&](const vector<int> &T) {
        nT3++;
        // Q: path of T from r to c; first arc entering A
        vector<int> Q; { int x2 = c; while (x2 != r) { Q.push_back(T[x2]); x2 = A[T[x2]].u; } reverse(Q.begin(), Q.end()); }
        int first = -1; for (int a : Q) if (inA[A[a].v] && !inA[A[a].u]) { first = a; break; }
        if (first < 0) { bad("L3_no_entry", n, r, A, chosen, c); return; }
        ll wT = 0; for (int v = 0; v < n; v++) if (v != r) wT += A[T[v]].w;
        ll wTp = A[first].w + d[A[first].v] - beta; if (MUT == 2) wTp = A[first].w - beta;
        vector<int> par(k, -1);
        par[aid] = id[A[first].u];
        for (int v = 0; v < n; v++) if (!inA[v] && v != r) {
          wTp += A[T[v]].w; par[id[v]] = id[A[T[v]].u];
        }
        bool ok = true; for (int v = 0; v < k; v++) { int xx = v, g = 0; while (xx != id[r] && g <= k + 1) { xx = par[xx]; g++; } if (xx != id[r]) ok = false; }
        if (!ok) bad("L3_not_arborescence", n, r, A, chosen, c);
        else if (wTp > wT - beta) bad("L3_weight", n, r, A, chosen, c);
      });
    }
  }
  // L4: all active components at once, on names, with one choice of c, of the arc of beta
  if (actives.size() >= 2) {
    vector<int> name(n); for (int i = 0; i < n; i++) name[i] = i;
    vector<int> ch2 = chosen;
    for (int K : actives) {
      int s = -1; for (int v = 0; v < n; v++) if (fd(v) == K) { s = v; break; }
      int x = s; for (int i = 0; i < n + 1; i++) x = A[chosen[x]].u; int c = x;
      vector<ll> d(n, INF); d[c] = 0;
      for (int i = 0; i < n; i++) for (auto &a : A) if (fd(a.u) == K && fd(a.v) == K && d[a.v] < INF && d[a.v] + a.w < d[a.u]) d[a.u] = d[a.v] + a.w;
      ll beta = INF; int barc = -1;
      for (int i = 0; i < (int)A.size(); i++) if (fd(A[i].u) != K && fd(A[i].v) == K && A[i].v != r && d[A[i].v] < INF && A[i].w + d[A[i].v] < beta) { beta = A[i].w + d[A[i].v]; barc = i; }
      for (int v = 0; v < n; v++) if (fd(v) == K && d[v] <= beta) name[v] = c;
      ch2[c] = barc;
    }
    // new components
    vector<int> uf(n); for (int i = 0; i < n; i++) uf[i] = i;
    function<int(int)> f2 = [&](int x) { return uf[x] == x ? x : uf[x] = f2(uf[x]); };
    for (int v = 0; v < n; v++) if (v != r && name[v] == v) uf[f2(v)] = f2(name[A[ch2[v]].u]);
    set<int> act2; for (int v = 0; v < n; v++) if (name[v] == v && f2(v) != f2(r)) act2.insert(f2(v));
    nL4++;
    if (2 * act2.size() > actives.size()) bad("L4_halving", n, r, A, chosen, -1);
  }
}
static void forStates(int n, int r, const vector<Arc> &A, ll cap) {
  // reached from r
  vector<char> seen(n, 0); seen[r] = 1; for (int i = 0; i < n; i++) for (auto &a : A) if (seen[a.u]) seen[a.v] = 1;
  for (int v = 0; v < n; v++) if (!seen[v]) return;
  vector<Arc> B; for (auto &a : A) if (a.v != r) B.push_back(a);
  vector<vector<int>> z(n); for (int i = 0; i < (int)B.size(); i++) if (B[i].w == 0) z[B[i].v].push_back(i);
  for (int v = 0; v < n; v++) if (v != r && z[v].empty()) return;
  vector<int> chosen(n, -1); ll done = 0;
  function<void(int)> go = [&](int v) {
    if (done >= cap) return;
    if (v == n) { done++; checkState(n, r, B, chosen); return; }
    if (v == r) { go(v + 1); return; }
    for (int a : z[v]) { chosen[v] = a; go(v + 1); }
  };
  go(0);
}
int main(int argc, char **argv) {
  // lem pool a b weights(csv) budgetPerGraph seed secs parallel mut
  ifstream f(argv[1]); int a = atoi(argv[2]), b = atoi(argv[3]);
  vector<ll> ws; { string t = argv[4]; size_t p = 0; while (true) { size_t q = t.find(',', p); ws.push_back(atoll(t.substr(p, q == string::npos ? q : q - p).c_str())); if (q == string::npos) break; p = q + 1; } }
  ll budget = atoll(argv[5]); mt19937_64 rng(atoll(argv[6])); double secs = atof(argv[7]); int par = atoi(argv[8]); MUT = atoi(argv[9]);
  int N; f >> N; vector<Graph> pool(N);
  for (auto &G : pool) { int m; f >> G.label >> G.n >> m; G.E.resize(m); for (auto &e : G.E) f >> e.first >> e.second; }
  auto t0 = chrono::steady_clock::now(); auto el = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
  ll inst = 0; int fullG = 0, sampG = 0;
  for (auto &G : pool) if (G.n >= a && G.n <= b) {
    if (el() > secs) break;
    int slots = 2 * G.E.size() * (1 + par); int base = ws.size() + 1;
    double tot = 1; for (int i = 0; i < slots; i++) tot *= base;
    bool full = tot * G.n <= budget; (full ? fullG : sampG)++;
    ll cnt = full ? (ll)(tot + 0.5) : budget;
    for (ll c = 0; c < cnt; c++) {
      if ((c & 255) == 0 && el() > secs) break;
      vector<Arc> A; ll x = c;
      for (int k = 0; k < slots; k++) {
        int dig = full ? (int)(x % base) : (int)(rng() % base); x /= base;
        if (!dig) continue;
        auto &e = G.E[(k / (1 + par)) / 2]; bool fw = (k / (1 + par)) % 2 == 0;
        A.push_back(fw ? Arc{e.first, e.second, ws[dig - 1]} : Arc{e.second, e.first, ws[dig - 1]});
      }
      if (full) { for (int r = 0; r < G.n; r++) { forStates(G.n, r, A, 400); inst++; } }
      else { forStates(G.n, (int)(rng() % G.n), A, 400); inst++; }
    }
  }
  printf("lem mut=%d n=[%d,%d] weights=%s parallel=%d full_graphs=%d sampled_graphs=%d instances=%lld states=%lld contractions=%lld T_in_L2=%lld T_in_L3=%lld eq=%lld L4=%lld secs=%.1f\n", MUT, a, b, argv[4], par, fullG, sampG, inst, nStates, nContr, nT2, nT3, nEq, nL4, el());
  printf(" cov d_inf=%lld partial=%lld d_eq_beta_noncycle=%lld pi_last_arc_is_chosen_of_c=%lld\n", nInf, nPartial, nTieA, nLastChosen);
  printf(" FAILS=%lld", fails); for (auto &kv : failCodes) printf(" %s=%lld", kv.first.c_str(), kv.second); printf("\n");
  return fails && MUT == 0 ? 1 : 0;
}
