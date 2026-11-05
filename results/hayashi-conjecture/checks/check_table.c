/* Checker B, part 2: a finite quandle given by its operation table.
   Input: n, then a binary file of n*n little-endian uint16, T[x*n + y] = x * y.
   Checks, over all elements and triples:
     idempotence x * x = x; each right translation R_y = (x -> x * y) is a
     bijection; right self-distributivity (x * y) * z = (x * z) * (y * z);
   then connectedness (orbit of 0 under all R_y), the cycle type of every R_y
   (all equal for a connected quandle), and whether the longest cycle length
   is a multiple of every other length (Hayashi's conjecture).
   Optional third and fourth arguments z0 z1 restrict the distributivity
   check to z in [z0, z1), to split the run into pieces; the remaining
   checks run only when z0 = z1 (no distributivity) or with no range.
   usage: checktable N FILE [z0 z1] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage\n"); return 2; }
  long n = atol(argv[1]);
  long z0 = argc > 3 ? atol(argv[3]) : 0, z1 = argc > 4 ? atol(argv[4]) : n;
  uint16_t *T = malloc(sizeof(uint16_t) * n * n);
  FILE *f = fopen(argv[2], "rb");
  if (!f || fread(T, sizeof(uint16_t), n * n, f) != (size_t)(n * n)) { fprintf(stderr, "read\n"); return 2; }
  fclose(f);
  for (long i = 0; i < n * n; i++) if (T[i] >= n) { printf("FAIL entry out of range\n"); return 1; }
  for (long x = 0; x < n; x++) if (T[x * n + x] != x) { printf("FAIL idempotence at %ld\n", x); return 1; }
  char *hit = malloc(n);
  for (long y = 0; y < n; y++) {
    memset(hit, 0, n);
    for (long x = 0; x < n; x++) { if (hit[T[x * n + y]]) { printf("FAIL R_%ld not bijective\n", y); return 1; } hit[T[x * n + y]] = 1; }
  }
  printf("idempotent; every right translation is a bijection\n");
  for (long z = z0; z < z1; z++)
    for (long y = 0; y < n; y++) {
      long yz = T[y * n + z];
      for (long x = 0; x < n; x++)
        if (T[(long)T[x * n + y] * n + z] != T[(long)T[x * n + z] * n + yz]) {
          printf("FAIL distributivity x=%ld y=%ld z=%ld\n", x, y, z); return 1; }
    }
  printf("right self-distributive for z in [%ld, %ld)\n", z0, z1);
  if (argc > 3 && z0 != z1) return 0;
  /* connectedness: orbit of 0 under all R_y */
  long *queue = malloc(sizeof(long) * n), qh = 0, qt = 0;
  memset(hit, 0, n); hit[0] = 1; queue[qt++] = 0;
  while (qh < qt) { long x = queue[qh++];
    for (long y = 0; y < n; y++) { long w = T[x * n + y]; if (!hit[w]) { hit[w] = 1; queue[qt++] = w; } } }
  printf("orbit of element 0: %ld of %ld -> %s\n", qt, n, qt == n ? "connected" : "NOT connected");
  /* cycle type of each R_y */
  long *cnt = calloc(n + 1, sizeof(long)), *cnt0 = calloc(n + 1, sizeof(long));
  int same = 1;
  for (long y = 0; y < n; y++) {
    memset(cnt, 0, sizeof(long) * (n + 1)); memset(hit, 0, n);
    for (long x = 0; x < n; x++) if (!hit[x]) { long L = 0, w = x; while (!hit[w]) { hit[w] = 1; w = T[w * n + y]; L++; } cnt[L]++; }
    if (y == 0) memcpy(cnt0, cnt, sizeof(long) * (n + 1));
    else if (memcmp(cnt0, cnt, sizeof(long) * (n + 1))) same = 0;
  }
  printf("all right translations have the same cycle type: %s\n", same ? "yes" : "no");
  if (qt != n) { printf("REJECT: not connected\n"); return 1; }
  if (!same) { printf("REJECT: right translations differ in cycle type\n"); return 1; }
  long lmax = 0; printf("profile (length^count):");
  for (long L = 1; L <= n; L++) if (cnt0[L]) { printf(" %ld^%ld", L, cnt0[L]); lmax = L; }
  printf("\nlongest %ld; lengths not dividing it:", lmax);
  int bad = 0;
  for (long L = 1; L <= n; L++) if (cnt0[L] && lmax % L) { printf(" %ld", L); bad = 1; }
  printf("\n");
  if (!bad) { printf("REJECT: every cycle length divides the longest\n"); return 1; }
  /* faithfulness: distinct columns */
  int faithful = 1;
  for (long y = 1; y < n && faithful; y++) for (long y2 = 0; y2 < y; y2++) {
    long x = 0; while (x < n && T[x * n + y] == T[x * n + y2]) x++;
    if (x == n) { faithful = 0; break; } }
  printf("faithful (distinct right translations): %s\n", faithful ? "yes" : "no");
  printf("ACCEPT: connected quandle; Hayashi's conjecture fails\n");
  return 0;
}
