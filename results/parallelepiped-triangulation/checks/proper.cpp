// Exact proper-intersection test for lattice simplices in any dimension d <= 6.
// Two full-dimensional simplices A, B intersect properly (in a common face) iff no
// circuit (Z+, Z-) of A u B has Z+ in A and Z- in B (De Loera-Rambau-Santos, Thm 4.1.3).
// Input (stdin): d; n points (d ints each); m simplices (d+1 point indices each);
// then q pairs to test (q = -1: all pairs). Output: the improper pairs "a b".
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int d; vector<vector<ll>> P; vector<vector<int>> S;
static ll det(vector<vector<ll>> M) {  // Bareiss, exact for integer input
  int n = M.size(); if (!n) return 1; ll sign = 1, prev = 1;
  for (int i = 0; i < n - 1; i++) {
    if (M[i][i] == 0) { int r = -1; for (int k = i + 1; k < n; k++) if (M[k][i]) { r = k; break; }
      if (r < 0) return 0; swap(M[i], M[r]); sign = -sign; }
    for (int j = i + 1; j < n; j++) for (int k = i + 1; k < n; k++)
      M[j][k] = (M[j][k] * M[i][i] - M[j][i] * M[i][k]) / prev;
    prev = M[i][i];
  }
  return sign * M[n - 1][n - 1];
}
// s is a circuit iff the (d+1) x k lifted matrix has rank k-1 and a kernel vector of full support
static bool circuit(const vector<int>& s, vector<ll>& w) {
  int k = s.size(), m = k - 1, R = d + 1;
  auto ent = [&](int r, int c) -> ll { return r < d ? P[s[c]][r] : 1; };
  for (int mask = 0; mask < (1 << R); mask++) {
    if (__builtin_popcount(mask) != m) continue;
    vector<int> rows; for (int r = 0; r < R; r++) if (mask >> r & 1) rows.push_back(r);
    w.assign(k, 0); bool nz = false;
    for (int j = 0; j < k; j++) {
      vector<vector<ll>> M(m, vector<ll>(m));
      for (int a = 0; a < m; a++) { int cc = 0; for (int c = 0; c < k; c++) if (c != j) M[a][cc++] = ent(rows[a], c); }
      w[j] = ((j & 1) ? -1 : 1) * det(M); if (w[j]) nz = true;
    }
    if (!nz) continue;
    for (int r = 0; r < R; r++) { ll t = 0; for (int c = 0; c < k; c++) t += ent(r, c) * w[c]; if (t) return false; }
    for (int j = 0; j < k; j++) if (!w[j]) return false;
    return true;
  }
  return false;
}
static bool improper(int a, int b) {
  auto& A = S[a]; auto& B = S[b];
  auto in = [](const vector<int>& X, int p) { return find(X.begin(), X.end(), p) != X.end(); };
  vector<int> U(A); for (int x : B) if (!in(A, x)) U.push_back(x);
  int m = U.size();
  for (int mask = 1; mask < (1 << m); mask++) {
    int k = __builtin_popcount(mask); if (k < 3 || k > d + 2) continue;
    vector<int> s; for (int i = 0; i < m; i++) if (mask >> i & 1) s.push_back(U[i]);
    vector<ll> w; if (!circuit(s, w)) continue;
    for (int sg = -1; sg <= 1; sg += 2) { bool ok = true;
      for (int i = 0; i < k && ok; i++) { ll c = w[i] * sg; if (c > 0 && !in(A, s[i])) ok = false; if (c < 0 && !in(B, s[i])) ok = false; }
      if (ok) return true; }
  }
  return false;
}
int main() {
  int n, m, q; if (scanf("%d %d", &d, &n) != 2) return 1;
  P.assign(n, vector<ll>(d)); for (auto& p : P) for (auto& x : p) scanf("%lld", &x);
  scanf("%d", &m); S.assign(m, vector<int>(d + 1)); for (auto& s : S) for (auto& x : s) scanf("%d", &x);
  scanf("%d", &q); vector<pair<int, int>> todo;
  if (q < 0) { for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) todo.push_back({a, b}); }
  else for (int i = 0; i < q; i++) { int a, b; scanf("%d %d", &a, &b); todo.push_back({a, b}); }
  for (auto [a, b] : todo) if (improper(a, b)) printf("%d %d\n", a, b);
}
