// p3path: decide whether a DIMACS formula from encode.py, plus a cube, has a
// model whose colouring of K_n has no monochromatic path on m vertices.
// Path clauses (not all edges of this path have colour c) are supplied
// lazily by an IPASIR-UP external propagator and logged, one per line, to
// the clause log; the DRAT proof is checked against CNF + cube + log.
//
// usage: p3path CNF n m [--cube "l1 l2 ..."] [--proof FILE] [--log FILE] [--set opt=val]
//                       [--model FILE] [--forget] [--quiet]
// exit 10 SAT (model written), 20 UNSAT, 0 unknown.
#include "cadical.hpp"
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <unordered_set>
#include <map>
#include <sstream>
#include <fstream>
#include <chrono>
#include <algorithm>
#include <functional>
using namespace std;

static int n, m, NE;
static int eid[32][32];
static vector<pair<int, int>> E;
static inline int X(int e, int c) { return 3 * e + c + 1; }

struct PathProp : CaDiCaL::ExternalPropagator {
  vector<signed char> val;      // by variable: 0 unassigned, 1 true, -1 false
  vector<int> trail;            // observed literals in assignment order
  vector<size_t> lim;           // trail size at each decision level
  uint32_t T[3][32], F[3][32];  // T: edge known colour c; F: known not c
  vector<int> todo;             // e*3+c newly true
  vector<vector<int>> ext;      // pending external clauses (conflicts)
  vector<int> props;            // pending propagation literals
  map<int, vector<int>> reason; // propagated literal -> clause
  vector<int> cur; size_t curpos = 0; bool reading = false;
  unordered_set<string> seen;
  FILE *logf = nullptr;
  long long nclauses = 0, nprops = 0, nconf = 0, nsearch = 0;
  // search scratch
  int sc_c; int path[64]; int plen; int unkEdge; int found_cap;

  PathProp () {
    val.assign (3 * NE + 1, 0);
    memset (T, 0, sizeof T); memset (F, 0, sizeof F);
  }
  void setv (int lit, int s) {
    int v = abs (lit); int e = (v - 1) / 3, c = (v - 1) % 3;
    int a = E[e].first, b = E[e].second;
    bool pos = (lit > 0) == (s > 0);
    if (s == 0) {
      // undo
      if (val[v] > 0) { T[c][a] &= ~(1u << b); T[c][b] &= ~(1u << a); }
      else if (val[v] < 0) { F[c][a] &= ~(1u << b); F[c][b] &= ~(1u << a); }
      val[v] = 0; return;
    }
    if (pos) { val[v] = 1; T[c][a] |= 1u << b; T[c][b] |= 1u << a; todo.push_back (e * 3 + c); }
    else { val[v] = -1; F[c][a] |= 1u << b; F[c][b] |= 1u << a; }
  }
  void notify_assignment (const vector<int> &lits) override {
    for (int l : lits) {
      if (val[abs (l)] != 0) continue;
      setv (l, 1); trail.push_back (l);
    }
  }
  void notify_new_decision_level () override { lim.push_back (trail.size ()); }
  void notify_backtrack (size_t L) override {
    size_t to = lim[L];
    while (trail.size () > to) { setv (trail.back (), 0); trail.pop_back (); }
    lim.resize (L);
    todo.clear (); props.clear ();
  }
  // log a clause handed to the solver (deduplicated)
  void logc (const vector<int> &cl) {
    vector<int> key = cl; sort (key.begin (), key.end ());
    string ks ((char *) key.data (), key.size () * sizeof (int));
    if (!seen.insert (ks).second) return;
    nclauses++;
    if (!logf) return;
    for (int l : key) fprintf (logf, "%d ", l);
    fprintf (logf, "0\n");
  }
  // record a path clause for colour c on vertex sequence p[0..m-1]
  void emit (int c, const int *p) {
    vector<int> cl;
    for (int i = 0; i + 1 < m; i++) cl.push_back (-X (eid[p[i]][p[i + 1]], c));
    int unk = 0, ulit = 0;
    for (int l : cl) { int v = val[-l]; if (v == 0) { unk++; ulit = l; } else if (v < 0) return; }
    if (unk == 0) { ext.push_back (cl); nconf++; }
    else if (unk == 1) {
      reason[ulit] = cl;
      props.push_back (ulit); nprops++;
    }
  }
  // available edges for colour c from v: not known-not-c
  inline uint32_t avail (int c, int v) { return ~F[c][v] & ~(1u << v) & ((1u << n) - 1); }
  // number of vertices reachable from v in avail graph avoiding mask
  int reach (int c, int v, uint32_t mask) {
    uint32_t seenm = 1u << v, front = 1u << v;
    while (front) {
      uint32_t nf = 0;
      for (uint32_t f = front; f; f &= f - 1) { int w = __builtin_ctz (f); nf |= avail (c, w); }
      nf &= ~seenm & ~mask; seenm |= nf; front = nf;
    }
    return __builtin_popcount (seenm);
  }
  // extend right end (from vertex v) by 'need' edges; left part fixed
  int lbuf[64], rbuf[64];
  bool right (int c, int v, uint32_t mask, int need, int unk, int llen, int rlen) {
    if (need == 0) {
      int p[64], k = 0;
      for (int i = llen - 1; i >= 0; i--) p[k++] = lbuf[i];
      for (int i = 0; i < rlen; i++) p[k++] = rbuf[i];
      emit (c, p);
      return --found_cap <= 0;
    }
    if (reach (c, v, mask & ~(1u << v)) - 1 < need) return false;
    for (uint32_t nb = avail (c, v) & ~mask; nb; nb &= nb - 1) {
      int w = __builtin_ctz (nb);
      int u2 = unk + !((T[c][v] >> w) & 1);
      if (u2 > 1) continue;
      rbuf[rlen] = w;
      if (right (c, w, mask | 1u << w, need - 1, u2, llen, rlen + 1)) return true;
    }
    return false;
  }
  bool left (int c, int u, int v, uint32_t mask, int a, int unk, int llen) {
    // left part has 'a' edges so far, ends at u; try right side with m-2-a
    int need = m - 2 - a;
    if (right (c, v, mask, need, unk, llen, 1)) return true;
    if (need == 0) return false;
    if (reach (c, u, mask & ~(1u << u)) - 1 < 1) return false;
    for (uint32_t nb = avail (c, u) & ~mask; nb; nb &= nb - 1) {
      int w = __builtin_ctz (nb);
      int u2 = unk + !((T[c][u] >> w) & 1);
      if (u2 > 1) continue;
      lbuf[llen] = w;
      if (left (c, w, v, mask | 1u << w, a + 1, u2, llen + 1)) return true;
    }
    return false;
  }
  void search_edge (int e, int c) {
    int u = E[e].first, v = E[e].second;
    nsearch++;
    found_cap = 64;
    lbuf[0] = u; rbuf[0] = v;
    left (c, u, v, (1u << u) | (1u << v), 0, 0, 1);
  }
  void drain () {
    while (!todo.empty () && ext.empty ()) {
      int ec = todo.back (); todo.pop_back ();
      int e = ec / 3, c = ec % 3;
      if (val[X (e, c)] != 1) continue;
      search_edge (e, c);
    }
  }
  int cb_propagate () override {
    for (;;) {
      while (!props.empty ()) {
        if (!ext.empty ()) return 0;
        int l = props.back (); props.pop_back ();
        if (val[abs (l)] == 0) return l;
      }
      if (todo.empty () || !ext.empty ()) return 0;
      drain ();
      if (props.empty ()) return 0;
    }
  }
  int cb_add_reason_clause_lit (int plit) override {
    if (!reading) { cur = reason[plit]; curpos = 0; reading = true; logc (cur); }
    if (curpos < cur.size ()) return cur[curpos++];
    reading = false; return 0;
  }
  bool cb_has_external_clause (bool &forget) override {
    forget = false;
    return !ext.empty ();
  }
  int cb_add_external_clause_lit () override {
    if (!reading) { cur = ext.back (); ext.pop_back (); curpos = 0; reading = true; logc (cur); }
    if (curpos < cur.size ()) return cur[curpos++];
    reading = false; return 0;
  }
  // full check on a complete model: DFS for a monochromatic P_m
  bool dfs_full (int c, const uint32_t *adj, int v, uint32_t mask, int len, int *p) {
    p[len - 1] = v;
    if (len == m) { emit (c, p); return true; }
    for (uint32_t nb = adj[v] & ~mask; nb; nb &= nb - 1) {
      int w = __builtin_ctz (nb);
      if (dfs_full (c, adj, w, mask | 1u << w, len + 1, p)) return true;
    }
    return false;
  }
  bool cb_check_found_model (const vector<int> &model) override {
    uint32_t adj[3][32]; memset (adj, 0, sizeof adj);
    for (int l : model) if (l > 0 && l <= 3 * NE) {
      int e = (l - 1) / 3, c = (l - 1) % 3;
      adj[c][E[e].first] |= 1u << E[e].second; adj[c][E[e].second] |= 1u << E[e].first;
    }
    // emit() consults val[]; make it reflect the model
    vector<signed char> save = val;
    for (int l : model) if (abs (l) <= 3 * NE) val[abs (l)] = l > 0 ? 1 : -1;
    bool bad = false; int p[64];
    for (int c = 0; c < 3 && !bad; c++)
      for (int s = 0; s < n && !bad; s++) bad = dfs_full (c, adj[c], s, 1u << s, 1, p);
    val = save;
    return !bad;
  }
};

int main (int argc, char **argv) {
  if (argc < 4) { fprintf (stderr, "usage\n"); return 1; }
  const char *cnf = argv[1]; n = atoi (argv[2]); m = atoi (argv[3]);
  vector<string> setopts;
  string cube, proof, logp, modelp, cubesp; bool quiet = false; int gdepth = 0;
  for (int i = 4; i < argc; i++) {
    string a = argv[i];
    if (a == "--cube") cube = argv[++i];
    else if (a == "--proof") proof = argv[++i];
    else if (a == "--log") logp = argv[++i];
    else if (a == "--model") modelp = argv[++i];
    else if (a == "--quiet") quiet = true;
    else if (a == "--set") setopts.push_back (argv[++i]);
    else if (a == "--gencubes") { gdepth = atoi (argv[++i]); cubesp = argv[++i]; }
  }
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) { eid[i][j] = eid[j][i] = E.size (); E.push_back ({i, j}); }
  NE = E.size ();
  auto t0 = chrono::steady_clock::now ();
  CaDiCaL::Solver S;
  for (auto &o : setopts) {   // --set name=value: a CaDiCaL option
    size_t eq = o.find ('='); string k = o.substr (0, eq); int v = atoi (o.c_str () + eq + 1);
    if (!S.set (k.c_str (), v)) { fprintf (stderr, "bad option %s\n", o.c_str ()); return 1; }
  }
  if (!proof.empty ()) { S.set ("binary", 1); S.trace_proof (proof.c_str ()); }
  int maxvar; bool ok;
  // read DIMACS
  {
    FILE *f = fopen (cnf, "r"); if (!f) { perror (cnf); return 1; }
    char line[1 << 16]; vector<int> cl;
    while (fgets (line, sizeof line, f)) {
      if (line[0] == 'c' || line[0] == 'p') continue;
      char *s = line; char *end;
      for (;;) { long v = strtol (s, &end, 10); if (end == s) break; s = end;
        if (v == 0) { for (int l : cl) S.add (l); S.add (0); cl.clear (); } else cl.push_back (v); }
    }
    fclose (f);
  }
  {
    istringstream is (cube); int l;
    while (is >> l) if (l) { S.add (l); S.add (0); }
  }
  PathProp P;
  if (!logp.empty ()) P.logf = fopen (logp.c_str (), "w");
  S.connect_external_propagator (&P);
  for (int v = 1; v <= 3 * NE; v++) S.add_observed_var (v);
  if (gdepth) {
    // Cube generation: depth-first over the first gdepth edges (row-wise)
    // whose colour the formula leaves open; each node assumes one colour
    // per edge and propagates (conflict limit 0).  Refuted prefixes are
    // dropped; the coverage check refutes CNF + log + negated cubes.
    vector<int> order;
    for (int e = 0; e < NE; e++) order.push_back (e);
    FILE *cf = fopen (cubesp.c_str (), "w");
    long long ncubes = 0, nref = 0, nsat = 0;
    vector<int> pre;
    function<void (size_t, int)> rec = [&] (size_t pos, int depth) {
      if (depth == gdepth || pos == order.size ()) {
        for (int l : pre) fprintf (cf, "%d ", l);
        fprintf (cf, "0\n"); ncubes++; return;
      }
      int e = order[pos];
      int live = 0;
      for (int c = 0; c < 3; c++) {
        for (int l : pre) S.assume (l);
        S.assume (X (e, c));
        int r = S.propagate ();
        if (r == 20) { nref++; continue; }
        if (r == 10) { nsat++; fprintf (stderr, "SAT during cube generation\n"); }
        live++;
      }
      // an edge whose colour is forced (one live value) does not count as a split
      int nd = depth + (live > 1);
      for (int c = 0; c < 3; c++) {
        for (int l : pre) S.assume (l);
        S.assume (X (e, c));
        if (S.propagate () == 20) continue;
        pre.push_back (X (e, c)); rec (pos + 1, nd); pre.pop_back ();
      }
    };
    rec (0, 0);
    fclose (cf);
    if (P.logf) fclose (P.logf);
    printf ("gencubes depth=%d cubes=%lld refuted=%lld sat=%lld clauses=%lld\n", gdepth, ncubes, nref, nsat, P.nclauses);
    S.disconnect_external_propagator ();
    return 0;
  }
  int res = S.solve ();
  double secs = chrono::duration<double> (chrono::steady_clock::now () - t0).count ();
  if (P.logf) fclose (P.logf);
  printf ("n=%d m=%d res=%s time=%.2f clauses=%lld props=%lld confl=%lld searches=%lld\n", n, m,
          res == 10 ? "SAT" : res == 20 ? "UNSAT" : "UNKNOWN", secs, P.nclauses, P.nprops, P.nconf, P.nsearch);
  if (res == 10 && !modelp.empty ()) {
    FILE *f = fopen (modelp.c_str (), "w");
    for (int e = 0; e < NE; e++) for (int c = 0; c < 3; c++) if (S.val (X (e, c)) > 0)
      fprintf (f, "%d %d %d\n", E[e].first, E[e].second, c);
    fclose (f);
  }
  S.disconnect_external_propagator ();
  return res;
}
