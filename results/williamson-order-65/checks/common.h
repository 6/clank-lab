/* Shared definitions for the independent CPU replay (order n odd, n <= 65).
   Written from the problem statement only; no code from the earlier search. */
#ifndef W_COMMON_H
#define W_COMMON_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXN 65
#define MAXH 32

typedef struct {
  int n, H;          /* order and number of free sign bits */
  int m, L;          /* compression factor m, compressed length L = n/m */
  int nr;            /* number of allowed signed rowsums */
  int rs[64];        /* allowed signed rowsums */
  double cs[MAXN];   /* cs[j] = cos(2 pi j / n) */
} params;

/* Row entries: x[0]=+1, x[i]=x[n-i]=-1 iff bit i-1 of mask is set. */
static inline void row_of_mask(const params *P, uint32_t mask, int *x) {
  x[0] = 1;
  for (int i = 1; i <= P->H; i++) {
    int v = ((mask >> (i - 1)) & 1) ? -1 : 1;
    x[i] = v; x[P->n - i] = v;
  }
}

static inline int rowsum_of_mask(const params *P, uint32_t mask) {
  return P->n - 4 * __builtin_popcount(mask);
}

/* Allowed signed rowsums: r == n (mod 4), and |r| occurs in some
   decomposition 4n = r1^2+r2^2+r3^2+r4^2 with all ri odd positive. */
static void params_init(params *P, int n, int m) {
  memset(P, 0, sizeof *P);
  P->n = n; P->H = (n - 1) / 2; P->m = m; P->L = m ? n / m : 0;
  int used[MAXN * 2 + 1] = {0};
  for (int a = 1; a * a <= 4 * n; a += 2)
    for (int b = a; a * a + b * b <= 4 * n; b += 2)
      for (int c = b; a * a + b * b + c * c <= 4 * n; c += 2)
        for (int d = c; a * a + b * b + c * c + d * d <= 4 * n; d += 2)
          if (a * a + b * b + c * c + d * d == 4 * n) used[a] = used[b] = used[c] = used[d] = 1;
  for (int a = 1; a <= n; a += 2)
    if (used[a]) P->rs[P->nr++] = (((a - n) % 4 + 4) % 4 == 0) ? a : -a;
  for (int j = 0; j < n; j++) P->cs[j] = cos(2.0 * M_PI * (double)j / (double)n);
}

static inline int rowsum_allowed(const params *P, int r) {
  for (int i = 0; i < P->nr; i++) if (P->rs[i] == r) return 1;
  return 0;
}

/* Compressed vector X_j = sum_t x_{j+L t}, j = 0..(L-1)/2 (symmetric). */
static inline void compress_mask(const params *P, uint32_t mask, int *X) {
  int x[MAXN];
  row_of_mask(P, mask, x);
  for (int j = 0; j <= (P->L - 1) / 2; j++) {
    int s = 0;
    for (int t = 0; t < P->m; t++) s += x[j + P->L * t];
    X[j] = s;
  }
}

/* Class key: digits (X_j + m)/2 in base m+1, j = 0 most significant. */
static inline uint32_t key_of_X(const params *P, const int *X) {
  uint32_t k = 0;
  for (int j = 0; j <= (P->L - 1) / 2; j++) k = k * (uint32_t)(P->m + 1) + (uint32_t)((X[j] + P->m) / 2);
  return k;
}

static inline void X_of_key(const params *P, uint32_t k, int *X) {
  for (int j = (P->L - 1) / 2; j >= 0; j--) { X[j] = 2 * (int)(k % (uint32_t)(P->m + 1)) - P->m; k /= (uint32_t)(P->m + 1); }
}

/* PAF(s) = sum_i x_i x_{i+s}, s = 0..H, exact integers. */
static inline void paf_of_mask(const params *P, uint32_t mask, int *paf) {
  int x[MAXN];
  row_of_mask(P, mask, x);
  for (int s = 0; s <= P->H; s++) {
    int v = 0;
    for (int i = 0; i < P->n; i++) { int j = i + s; if (j >= P->n) j -= P->n; v += x[i] * x[j]; }
    paf[s] = v;
  }
}

/* Spectrum lambda(k) = sum_i x_i cos(2 pi i k / n), k = 1..H, computed directly
   (32 products of +-1 with a table entry); see the reductions in ../paper/paper.tex for the error bound. */
static inline double lambda_of_row(const params *P, const int *x, int k) {
  double s = 1.0;
  for (int i = 1; i <= P->H; i++) s += 2.0 * (double)x[i] * P->cs[(i * k) % P->n];
  return s;
}

static inline uint64_t splitmix64(uint64_t *st) {
  uint64_t z = (*st += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
#endif
