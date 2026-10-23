/* rows: enumerate every normalized symmetric row of odd order n (all 2^H masks),
   keep those with an allowed rowsum and lambda(k)^2 <= 4n (within a safe margin)
   for k = 1..H, and write them grouped by compressed class.
   Usage: rows n m outdir [nofilter]   |   rows n m --cos (print the cosine table)
   Output: outdir/rows.bin (uint32 masks sorted by (class key, mask)),
           outdir/classes.tsv (id key rowsum X_0..X_{(L-1)/2} count offset). */
#include "common.h"
#include <omp.h>

#define NCHUNK 64

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: rows n m outdir [nofilter]\n"); return 2; }
  int n = atoi(argv[1]), m = atoi(argv[2]);
  int nofilter = argc > 4 && !strcmp(argv[4], "nofilter");
  params P; params_init(&P, n, m);
  if (!strcmp(argv[3], "--cos")) { /* print the cosine table exactly (hex floats) for check_cos.py */
    for (int j = 0; j < n; j++) printf("%d %a\n", j, P.cs[j]);
    return 0;
  }
  if (n % 2 == 0 || n > MAXN || m < 1 || n % m) { fprintf(stderr, "bad n/m\n"); return 2; }
  int H = P.H, h1 = H / 2, h2 = H - h1;
  uint64_t total = 1ULL << H;
  uint32_t nkeys = 1; for (int j = 0; j <= (P.L - 1) / 2; j++) nkeys *= (uint32_t)(m + 1);
  double bound = 4.0 * n + 1e-6;
  /* Half tables: Tlo[lo][k] = sum_{i=1..h1} x_i cos(2 pi i k/n), Thi for i = h1+1..H. */
  size_t nlo = 1u << h1, nhi = 1u << h2;
  double *Tlo = malloc(nlo * (size_t)H * sizeof(double));
  double *Thi = malloc(nhi * (size_t)H * sizeof(double));
  for (size_t lo = 0; lo < nlo; lo++)
    for (int k = 1; k <= H; k++) {
      double s = 0;
      for (int i = 1; i <= h1; i++) s += (((lo >> (i - 1)) & 1) ? -1.0 : 1.0) * P.cs[(i * k) % n];
      Tlo[lo * H + (k - 1)] = s;
    }
  for (size_t hi = 0; hi < nhi; hi++)
    for (int k = 1; k <= H; k++) {
      double s = 0;
      for (int i = h1 + 1; i <= H; i++) s += (((hi >> (i - h1 - 1)) & 1) ? -1.0 : 1.0) * P.cs[(i * k) % n];
      Thi[hi * H + (k - 1)] = s;
    }
  int nchunk = total >= NCHUNK ? NCHUNK : 1;
  uint64_t csize = total / (uint64_t)nchunk;
  uint32_t *cnt = calloc((size_t)nchunk * nkeys, sizeof(uint32_t));
  uint32_t *rows = NULL;
  uint64_t *off = NULL;
  uint64_t kept = 0;
  for (int pass = 0; pass < 2; pass++) {
#pragma omp parallel for schedule(dynamic, 1)
    for (int c = 0; c < nchunk; c++) {
      uint32_t *cc = cnt + (size_t)c * nkeys;
      uint64_t *oo = pass ? off + (size_t)c * nkeys : NULL;
      for (uint64_t mk = (uint64_t)c * csize; mk < (uint64_t)(c + 1) * csize; mk++) {
        uint32_t mask = (uint32_t)mk;
        if (!rowsum_allowed(&P, rowsum_of_mask(&P, mask))) continue;
        if (!nofilter) {
          const double *a = Tlo + (size_t)(mask & (nlo - 1)) * H, *b = Thi + (size_t)(mask >> h1) * H;
          int bad = 0;
          for (int k = 0; k < H; k++) { double l = 1.0 + 2.0 * (a[k] + b[k]); if (l * l > bound) { bad = 1; break; } }
          if (bad) continue;
        }
        int X[MAXN]; compress_mask(&P, mask, X);
        uint32_t key = key_of_X(&P, X);
        if (!pass) cc[key]++; else rows[oo[key]++] = mask;
      }
    }
    if (!pass) {
      off = malloc((size_t)nchunk * nkeys * sizeof(uint64_t));
      uint64_t s = 0;
      for (uint32_t k = 0; k < nkeys; k++)
        for (int c = 0; c < nchunk; c++) { off[(size_t)c * nkeys + k] = s; s += cnt[(size_t)c * nkeys + k]; }
      kept = s;
      rows = malloc((kept ? kept : 1) * sizeof(uint32_t));
    }
  }
  char path[4096];
  snprintf(path, sizeof path, "%s/rows.bin", argv[3]);
  FILE *f = fopen(path, "wb");
  if (!f || fwrite(rows, sizeof(uint32_t), kept, f) != kept || fclose(f)) { fprintf(stderr, "write failed\n"); return 1; }
  snprintf(path, sizeof path, "%s/classes.tsv", argv[3]);
  f = fopen(path, "w");
  uint64_t o = 0; int id = 0;
  for (uint32_t k = 0; k < nkeys; k++) {
    uint64_t c = 0;
    for (int ch = 0; ch < nchunk; ch++) c += cnt[(size_t)ch * nkeys + k];
    if (!c) continue;
    int X[MAXN]; X_of_key(&P, k, X);
    int r = X[0]; for (int j = 1; j <= (P.L - 1) / 2; j++) r += 2 * X[j];
    fprintf(f, "%d\t%u\t%d\t", id++, k, r);
    for (int j = 0; j <= (P.L - 1) / 2; j++) fprintf(f, "%d%s", X[j], j < (P.L - 1) / 2 ? "," : "");
    fprintf(f, "\t%llu\t%llu\n", (unsigned long long)c, (unsigned long long)o);
    o += c;
  }
  if (fclose(f)) return 1;
  printf("n=%d m=%d H=%d masks=%llu kept=%llu classes=%d filter=%s\n", n, m, H, (unsigned long long)total,
         (unsigned long long)kept, id, nofilter ? "off" : "on");
  return 0;
}
