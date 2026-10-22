// ekg_gen.cpp -- EKG sequence generator and Conjecture 3 check.
//
// Written from the definition and the LRS pointer rule, independently of the
// outside verifier in ../external-2026-10-21 (not consulted).
//
//   a(1)=1, a(2)=2, a(n) = least unused m with gcd(m, a(n-1)) > 1.
//   Pointer rule: a(n) = min over primes q | a(n-1) of B_q, where B_q is the
//   least unused multiple of q.  (Any m sharing a factor with a(n-1) is a
//   multiple of some prime q | a(n-1), hence >= B_q; and each B_q qualifies.)
//
// Usage: ekg_gen N [seqfile|-] [X ...]
//   Checks 28 a(n) >= 13 n and 7 a(n) <= 12 n for n <= N, reports every
//   equality, and frontier statistics.  With seqfile, writes a(1..N) as
//   little-endian uint64.  For each threshold X: the first t with E(t) >= X
//   and max K(t) over states with E(t) < X.  Every 10^8 terms a line
//   "ckpt n a(n) E K maxK fnv64" (FNV-1a over a(1..n) as uint64 LE).  Value cap V = floor(12N/7)+2: a value above the
//   cap at index n <= N would itself violate 7a(n) <= 12n, so the run stops
//   there with a violation; a pointer beyond V is treated as infinite.
//
// Memory: per odd m <= V a uint32 (rank of spf(m) among odd primes), a used
// bitset, and one uint64 pointer per odd prime <= V.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <cmath>
#include <chrono>

typedef uint64_t u64;
typedef uint32_t u32;

static u64 V;                 // value cap
static std::vector<u32> spfr; // spfr[(m-1)/2] = rank of smallest prime factor of odd m>=3
static std::vector<u64> P;    // P[rank] = odd prime
static std::vector<u64> used; // bitset over 0..V+1
static std::vector<u64> ptr;  // ptr[rank] = current lower bound for B_q (0 = q)

static inline bool isused(u64 m) { return m > V ? false : (used[m >> 6] >> (m & 63)) & 1; }
static inline void setused(u64 m) { used[m >> 6] |= 1ULL << (m & 63); }

static void sieve() {
    u64 nodd = (V + 1) / 2;        // odd numbers 1,3,...,<=V : index i <-> 2i+1
    spfr.assign(nodd, 0xFFFFFFFFu);
    u64 r = (u64)std::sqrt((double)V) + 2;
    while (r * r > V) r--;
    // small odd primes up to r by a plain sieve
    std::vector<char> comp(r + 1, 0);
    std::vector<u64> small;
    for (u64 i = 3; i <= r; i += 2) {
        if (comp[i]) continue;
        small.push_back(i);
        for (u64 j = i * i; j <= r; j += 2 * i) comp[j] = 1;
    }
    // segmented marking: odd m in [lo, hi)
    const u64 SEG = 1ULL << 22;    // odd numbers per segment
    P.clear();
    P.reserve((size_t)(1.1 * V / std::log((double)V)) + 1000);
    std::vector<u64> next(small.size());
    for (size_t k = 0; k < small.size(); k++) next[k] = small[k] * small[k];
    for (u64 i0 = 1; i0 < nodd; i0 += SEG) {     // index range [i0, i1)
        u64 i1 = std::min(nodd, i0 + SEG);
        u64 hi = 2 * i1 + 1;                     // values < hi
        for (size_t k = 0; k < small.size(); k++) {
            u64 p = small[k];
            if (p * p >= hi) break;
            u64 m = next[k];
            // the rank of p is k (small primes are the first ranks, in order)
            for (; m < hi; m += 2 * p) {
                u32 &s = spfr[(m - 1) / 2];
                if (s == 0xFFFFFFFFu) s = (u32)k;
            }
            next[k] = m;
        }
        for (u64 i = i0; i < i1; i++) {
            if (spfr[i] == 0xFFFFFFFFu) {        // 2i+1 is prime
                spfr[i] = (u32)P.size();
                P.push_back(2 * i + 1);
            }
        }
    }
    // consistency: the first |small| ranks must be the small primes
    for (size_t k = 0; k < small.size(); k++)
        if (P[k] != small[k]) { fprintf(stderr, "rank mismatch\n"); exit(3); }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s N [seqfile|-] [X ...]\n", argv[0]); return 2; }
    u64 N = strtoull(argv[1], 0, 10);
    if (N < 3) { fprintf(stderr, "N >= 3\n"); return 2; }
    V = (12 * N) / 7 + 2;
    FILE *out = (argc > 2 && strcmp(argv[2], "-") != 0) ? fopen(argv[2], "wb") : 0;
    std::vector<u64> X; for (int i = 3; i < argc; i++) X.push_back(strtoull(argv[i], 0, 10));
    std::vector<u64> firstX(X.size(), 0); std::vector<long long> maxKX(X.size(), 0);
    auto t0 = std::chrono::steady_clock::now();
    sieve();
    if (P.size() >= 0xFFFFFFFFull) { fprintf(stderr, "too many primes\n"); return 3; }
    used.assign(V / 64 + 2, 0);
    ptr.assign(P.size(), 0);
    double tsieve = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    std::vector<u64> buf; buf.reserve(1 << 16);
    auto emit = [&](u64 v) { if (out) { buf.push_back(v); if (buf.size() == (1u << 16)) { fwrite(buf.data(), 8, buf.size(), out); buf.clear(); } } };

    u64 fnv = 14695981039346656037ULL;  // FNV-1a 64 offset basis
    auto fnvadd32 = [&](u64 v) { u32 w = (u32)v; for (int b = 0; b < 4; b++) { fnv ^= (w >> (8 * b)) & 255; fnv *= 1099511628211ULL; } };
    u64 fnv64 = 14695981039346656037ULL;
    auto fnvadd = [&](u64 v) { for (int b = 0; b < 8; b++) { fnv64 ^= (v >> (8 * b)) & 255; fnv64 *= 1099511628211ULL; } fnvadd32(v); };

    u64 B2 = 4;          // least unused even (E)
    long long K = 0;     // used evens above E
    long long maxK = 0, maxKbelow = 0; u64 firstE8 = 0;
    u64 violations = 0, nlow = 0, nup = 0;
    u64 prev = 2;
    setused(1); setused(2); emit(1); emit(2); fnvadd(1); fnvadd(2);
    // n=1,2: 28*1>=13, 7*1<=12; 28*2>=26, 7*2<=24: no equality, no violation.
    std::vector<u64> fac; fac.reserve(16);
    for (u64 n = 3; n <= N; n++) {
        // factor prev
        fac.clear();
        u64 m = prev;
        bool even = (m % 2 == 0);
        while (m % 2 == 0) m /= 2;
        while (m > 1) {
            u32 rk = spfr[(m - 1) / 2];
            u64 q = P[rk];
            fac.push_back(rk);
            do m /= q; while (m % q == 0);
        }
        u64 best = ~0ULL;
        if (even) best = B2;
        for (u64 rk : fac) {
            u64 q = P[rk];
            u64 b = ptr[rk] ? ptr[rk] : q;
            while (b <= V && isused(b)) b += q;
            ptr[rk] = b;
            if (b < best) best = b;
        }
        if (best > V) {
            printf("violation_cap n %llu\n", (unsigned long long)n);
            violations++;
            break;
        }
        u64 a = best;
        setused(a);
        emit(a); fnvadd(a);
        // bound checks, exact integers
        unsigned __int128 L = (unsigned __int128)28 * a, R13 = (unsigned __int128)13 * n;
        unsigned __int128 U7 = (unsigned __int128)7 * a, U12 = (unsigned __int128)12 * n;
        if (L < R13 || U7 > U12) { violations++; printf("violation n %llu a %llu\n", (unsigned long long)n, (unsigned long long)a); }
        if (L == R13) { nlow++; printf("lower_equality %llu %llu\n", (unsigned long long)n, (unsigned long long)a); }
        if (U7 == U12) { nup++; printf("upper_equality %llu %llu\n", (unsigned long long)n, (unsigned long long)a); }
        // frontier
        if (a % 2 == 0) {
            if (a == B2) {
                B2 += 2;
                while (isused(B2)) { B2 += 2; K--; }
            } else K++;
        }
        if (K > maxK) maxK = K;
        if (B2 < 100000000ULL) { if (K > maxKbelow) maxKbelow = K; }
        else if (!firstE8) firstE8 = n;
        for (size_t i = 0; i < X.size(); i++) {
            if (B2 < X[i]) { if (K > maxKX[i]) maxKX[i] = K; }
            else if (!firstX[i]) firstX[i] = n;
        }
        if (n % 100000000ULL == 0) {
            printf("ckpt %llu %llu %llu %lld %lld %016llx\n", (unsigned long long)n, (unsigned long long)a,
                   (unsigned long long)B2, K, maxK, (unsigned long long)fnv64);
            fflush(stdout);
        }
        prev = a;
    }
    if (out) { fwrite(buf.data(), 8, buf.size(), out); fclose(out); }
    double tall = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("N %llu cap %llu last %llu E %llu maxK %lld maxK_E_below_1e8 %lld first_t_E_ge_1e8 %llu\n",
           (unsigned long long)N, (unsigned long long)V, (unsigned long long)prev, (unsigned long long)B2,
           maxK, maxKbelow, (unsigned long long)firstE8);
    printf("violations %llu lower_equalities %llu upper_equalities %llu\n",
           (unsigned long long)violations, (unsigned long long)nlow, (unsigned long long)nup);
    printf("fnv1a64_u32le %016llx fnv1a64_u64le %016llx\n", (unsigned long long)fnv, (unsigned long long)fnv64);
    for (size_t i = 0; i < X.size(); i++)
        printf("threshold %llu first_t_E_ge %llu maxK_E_below %lld\n", (unsigned long long)X[i],
               (unsigned long long)firstX[i], maxKX[i]);
    printf("seconds_sieve %.1f seconds_total %.1f\n", tsieve, tall);
    bool ok = violations == 0 && nlow == 1 && nup == 1;
    return ok ? 0 : 1;
}
