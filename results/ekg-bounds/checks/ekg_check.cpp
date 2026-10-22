// ekg_check.cpp -- independent checker for an EKG prefix file.
//
// Reads a(1..N) (little-endian uint64) and accepts iff it is the EKG prefix:
//   a(1)=1, a(2)=2, the values are distinct, and for 3<=n<=N
//   (G) gcd(a(n), a(n-1)) > 1, and
//   (M) every m < a(n) with gcd(m, a(n-1)) > 1 occurs at an index < n.
// It shares no code with ekg_gen.cpp and uses a different method: no
// pointers and no factorization.  With z(m) the index of value m (infinity
// if absent), (M) says: for each prime q | a(n-1), max{ z(jq) : jq < a(n) } < n.
// For each prime q it builds the prefix maximum of z over the multiples of
// q, then walks those multiples m = jq that occur as some a(n-1), which
// enumerates exactly the pairs (n, q | a(n-1)), and answers each query.
//
// Then it checks 28a(n) >= 13n and 7a(n) <= 12n with exact integers, lists
// equalities, and recomputes the frontier facts by an independent replay:
// first t with E(t) >= X for the thresholds given, and max K(t) over the
// states with E(t) < X.
//
// Usage: ekg_check seqfile [X ...]      exit 0 iff accepted and the
// bounds hold with equality exactly at (7,12) and (28,13).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <numeric>
#include <algorithm>

typedef uint64_t u64;
typedef uint32_t u32;
static const u32 INF = 0xFFFFFFFFu;

static u64 gcdu(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s seqfile [X ...]\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("open"); return 2; }
    fseek(f, 0, SEEK_END); long long bytes = ftell(f); fseek(f, 0, SEEK_SET);
    if (bytes % 8) { printf("REJECT bad length\n"); return 1; }
    u64 N = bytes / 8;
    std::vector<u64> a(N + 1);
    if (fread(a.data() + 1, 8, N, f) != N) { printf("REJECT short read\n"); return 1; }
    fclose(f);
    if (N < 2 || N >= INF || a[1] != 1 || a[2] != 2) { printf("REJECT start\n"); return 1; }
    u64 maxv = 0;
    for (u64 n = 1; n <= N; n++) { if (a[n] == 0) { printf("REJECT zero\n"); return 1; } maxv = std::max(maxv, a[n]); }
    // positions
    std::vector<u32> z(maxv + 1, INF);
    for (u64 n = 1; n <= N; n++) {
        if (z[a[n]] != INF) { printf("REJECT repeat value %llu at %llu\n", (unsigned long long)a[n], (unsigned long long)n); return 1; }
        z[a[n]] = (u32)n;
    }
    // (G)
    for (u64 n = 3; n <= N; n++)
        if (gcdu(a[n], a[n - 1]) == 1) { printf("REJECT gcd at %llu\n", (unsigned long long)n); return 1; }
    // primes up to maxv: odd-only bit sieve
    std::vector<uint8_t> comp((maxv >> 4) + 1, 0);    // bit for odd m: index m>>1
    auto iscomp = [&](u64 m) { return (comp[m >> 4] >> ((m >> 1) & 7)) & 1; };
    for (u64 p = 3; p * p <= maxv; p += 2)
        if (!iscomp(p))
            for (u64 m = p * p; m <= maxv; m += 2 * p) comp[m >> 4] |= 1 << ((m >> 1) & 7);
    // (M) per prime
    u64 queries = 0;
    std::vector<u32> pm;
    for (u64 q = 2; q <= maxv; q = (q == 2 ? 3 : q + 2)) {
        if (q > 2 && iscomp(q)) continue;
        u64 J = maxv / q;
        // does any multiple of q occur as a(n-1) with 3<=n<=N ?  (skip work if not)
        pm.assign(J + 1, 0);
        u32 run = 0;
        bool any = false;
        for (u64 j = 1; j <= J; j++) {
            u32 zz = z[j * q];
            run = std::max(run, zz);   // INF dominates
            pm[j] = run;
            if (zz != INF && zz >= 2 && zz <= N - 1) any = true;
        }
        if (!any) continue;
        for (u64 j = 1; j <= J; j++) {
            u32 zz = z[j * q];
            if (zz == INF || zz < 2 || zz > N - 1) continue;
            u64 n = (u64)zz + 1;           // a(n-1) = jq, so q | a(n-1)
            u64 L = a[n];
            u64 jmax = (L - 1) / q;        // multiples jq < L
            if (jmax > J) jmax = J;        // beyond maxv: then L-1 >= maxv... see below
            if ((L - 1) / q > J) {
                // some multiple of q below L exceeds maxv, so it never occurs: reject
                printf("REJECT minimality n %llu q %llu (multiple beyond max)\n", (unsigned long long)n, (unsigned long long)q);
                return 1;
            }
            queries++;
            if (jmax >= 1 && pm[jmax] >= n) {
                printf("REJECT minimality n %llu q %llu\n", (unsigned long long)n, (unsigned long long)q);
                return 1;
            }
        }
    }
    // bounds
    u64 nlow = 0, nup = 0, viol = 0; bool eqok = true;
    for (u64 n = 1; n <= N; n++) {
        unsigned __int128 l = (unsigned __int128)28 * a[n], r = (unsigned __int128)13 * n;
        unsigned __int128 u = (unsigned __int128)7 * a[n], s = (unsigned __int128)12 * n;
        if (l < r || u > s) { viol++; printf("violation %llu %llu\n", (unsigned long long)n, (unsigned long long)a[n]); }
        if (l == r) { nlow++; if (!(n == 28 && a[n] == 13)) eqok = false; printf("lower_equality %llu %llu\n", (unsigned long long)n, (unsigned long long)a[n]); }
        if (u == s) { nup++; if (!(n == 7 && a[n] == 12)) eqok = false; printf("upper_equality %llu %llu\n", (unsigned long long)n, (unsigned long long)a[n]); }
    }
    // frontier replay: E(t) = least even not in {a(1..t)}, K(t) = #used evens > E(t)
    std::vector<u64> X;
    for (int i = 2; i < argc; i++) X.push_back(strtoull(argv[i], 0, 10));
    std::vector<u64> firstT(X.size(), 0);
    std::vector<long long> maxKbelow(X.size(), 0);
    {
        std::vector<uint8_t> ev((maxv >> 4) + 2, 0);   // bit for even m: index m>>1
        auto evset = [&](u64 m) { ev[m >> 4] |= 1 << ((m >> 1) & 7); };
        auto evget = [&](u64 m) { return m <= maxv + 1 && ((ev[m >> 4] >> ((m >> 1) & 7)) & 1); };
        u64 E = 2; long long K = 0;
        for (u64 t = 1; t <= N; t++) {
            u64 v = a[t];
            if (v % 2 == 0) {
                evset(v);
                if (v > E) K++;
                else if (v == E) { while (evget(E)) { E += 2; if (evget(E)) K--; } }
            }
            for (size_t i = 0; i < X.size(); i++) {
                if (E < X[i]) maxKbelow[i] = std::max(maxKbelow[i], K);
                else if (!firstT[i]) firstT[i] = t;
            }
        }
        printf("final_E %llu\n", (unsigned long long)E);
    }
    for (size_t i = 0; i < X.size(); i++)
        printf("threshold %llu first_t_E_ge %llu maxK_E_below %lld\n", (unsigned long long)X[i],
               (unsigned long long)firstT[i], maxKbelow[i]);
    printf("N %llu maxv %llu queries %llu violations %llu lower_eq %llu upper_eq %llu\n",
           (unsigned long long)N, (unsigned long long)maxv, (unsigned long long)queries,
           (unsigned long long)viol, (unsigned long long)nlow, (unsigned long long)nup);
    bool ok = viol == 0 && eqok && nlow == 1 && nup == 1;
    printf(ok ? "ACCEPT\n" : "REJECT bounds\n");
    return ok ? 0 : 1;
}
