/* baseline: reference enumeration of ALL ordered quadruples of normalized
   symmetric +-1 rows of odd order n with PAF_A+PAF_B+PAF_C+PAF_D = 0 at every
   nonzero shift. No compression, no spectral filter, no product theorem,
   no multiplier reduction. Rows are grouped only by rowsum (a solution
   has rA^2+rB^2+rC^2+rD^2 = 4n, as proved in ../paper/paper.tex); with "flat" even
   that grouping is skipped. Optional "rowfilter" drops rows with some
   lambda(k)^2 > 4n + 1e-6 (to test that filter alone, at larger n).
   Usage: baseline n [flat|rowfilter] > solutions (one line per ordered solution: 4 masks) */
#include "common.h"
#include <omp.h>

static params P;
typedef struct { uint64_t key; uint32_t a, b; } ent;

static void paf_direct(uint32_t mask, int *paf) { paf_of_mask(&P, mask, paf); }

int main(int argc, char **argv) {
  int n = atoi(argv[1]);
  int flat = argc > 2 && !strcmp(argv[2], "flat");
  int rowfilter = argc > 2 && !strcmp(argv[2], "rowfilter");
  params_init(&P, n, 0);
  int H = P.H; uint32_t NR = 1u << H;
  uint64_t st = 0x0bad5eed12345678ULL, R[MAXH + 1];
  for (int s = 0; s <= MAXH; s++) R[s] = splitmix64(&st) | 1;
  /* per-row hash and rowsum */
  uint64_t *h = malloc((size_t)NR * 8); int *rs = malloc((size_t)NR * sizeof(int)); uint8_t *keep = malloc(NR);
#pragma omp parallel for schedule(static)
  for (uint32_t mk = 0; mk < NR; mk++) {
    int paf[MAXH + 1]; paf_direct(mk, paf);
    uint64_t v = 0; for (int s = 1; s <= H; s++) v += (uint64_t)(int64_t)paf[s] * R[s];
    h[mk] = v; rs[mk] = rowsum_of_mask(&P, mk); keep[mk] = 1;
    if (rowfilter) {
      int x[MAXN]; row_of_mask(&P, mk, x);
      for (int k = 1; k <= H; k++) { double l = lambda_of_row(&P, x, k); if (l * l > 4.0 * n + 1e-6) { keep[mk] = 0; break; } }
    }
  }
  /* rowsum groups (signed rowsums n-4p, p = 0..H) */
  int ng = H + 1; uint32_t **G = malloc(ng * sizeof *G); uint32_t *gn = calloc(ng, sizeof(uint32_t));
  for (int g = 0; g < ng; g++) G[g] = malloc((size_t)NR * 4);
  for (uint32_t mk = 0; mk < NR; mk++) if (keep[mk]) { int g = flat ? 0 : __builtin_popcount(mk); G[g][gn[g]++] = mk; }
  if (flat) ng = 1;
  uint64_t nsol = 0;
  for (int g1 = 0; g1 < ng; g1++) for (int g2 = 0; g2 < ng; g2++) for (int g3 = 0; g3 < ng; g3++) for (int g4 = 0; g4 < ng; g4++) {
    if (!flat) {
      int r1 = n - 4 * g1, r2 = n - 4 * g2, r3 = n - 4 * g3, r4 = n - 4 * g4;
      if (r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 != 4 * n) continue;
    } else if (g1 || g2 || g3 || g4) continue;
    uint64_t na = (uint64_t)gn[g1] * gn[g2], nb = (uint64_t)gn[g3] * gn[g4];
    if (!na || !nb) continue;
    /* store all (A,B) pairs keyed by hA+hB in an open-addressing table, probe with -(hC+hD) */
    uint64_t tsz = 2; while (tsz < 2 * na + 2) tsz <<= 1;
    ent *T = calloc(tsz, sizeof(ent)); uint64_t tm = tsz - 1;
    for (uint32_t i = 0; i < gn[g1]; i++) for (uint32_t j = 0; j < gn[g2]; j++) {
      uint32_t a = G[g1][i], b = G[g2][j]; uint64_t k = h[a] + h[b]; if (!k) k = 1;
      uint64_t p = (k * 0xff51afd7ed558ccdULL) >> 7;
      for (p &= tm; T[p].key; p = (p + 1) & tm);
      T[p] = (ent){k, a, b};
    }
#pragma omp parallel for schedule(dynamic, 16) reduction(+:nsol)
    for (uint32_t i = 0; i < gn[g3]; i++) for (uint32_t j = 0; j < gn[g4]; j++) {
      uint32_t c = G[g3][i], d = G[g4][j]; uint64_t k = (uint64_t)0 - (h[c] + h[d]); if (!k) k = 1;
      uint64_t p = (k * 0xff51afd7ed558ccdULL) >> 7;
      for (p &= tm; T[p].key; p = (p + 1) & tm) {
        if (T[p].key != k) continue;
        uint32_t q[4] = {T[p].a, T[p].b, c, d}; int tot[MAXH + 1] = {0}, ok = 1;
        for (int r = 0; r < 4; r++) { int paf[MAXH + 1]; paf_direct(q[r], paf); for (int s = 1; s <= H; s++) tot[s] += paf[s]; }
        for (int s = 1; s <= H; s++) if (tot[s]) ok = 0;
        if (ok) {
          nsol++;
#pragma omp critical
          printf("%u\t%u\t%u\t%u\n", q[0], q[1], q[2], q[3]);
        }
      }
    }
    free(T);
  }
  fprintf(stderr, "baseline n=%d mode=%s ordered_normalized_solutions=%llu\n", n, flat ? "flat" : rowfilter ? "rowfilter" : "rowsum", (unsigned long long)nsol);
  return 0;
}
