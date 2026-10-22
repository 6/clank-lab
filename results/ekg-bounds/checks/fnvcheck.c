/* fnvcheck SEQFILE N HEX: FNV-1a 64 over the first N little-endian uint64
   terms of SEQFILE (the checkpoint hash of ekg_gen and finite/indep/ekgv).
   Exit 0 if it equals HEX, 1 otherwise.  Written for the prefix corruption
   receipt; shares no code with either generator. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
  if (c != 4) { fprintf(stderr, "usage: fnvcheck SEQFILE N HEX\n"); return 2; }
  FILE *f = fopen(v[1], "rb"); if (!f) { perror("open"); return 2; }
  uint64_t n = strtoull(v[2], 0, 10), want = strtoull(v[3], 0, 16), h = 14695981039346656037ULL, buf[65536];
  uint64_t done = 0;
  while (done < n) {
    size_t k = n - done < 65536 ? n - done : 65536;
    if (fread(buf, 8, k, f) != k) { fprintf(stderr, "short file\n"); return 2; }
    for (size_t i = 0; i < k; i++) for (int b = 0; b < 8; b++) { h ^= (buf[i] >> (8 * b)) & 255; h *= 1099511628211ULL; }
    done += k;
  }
  printf("fnv64 %016llx %s\n", (unsigned long long)h, h == want ? "MATCH" : "MISMATCH");
  return h == want ? 0 : 1;
}
