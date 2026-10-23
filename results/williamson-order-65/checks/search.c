/* search: exhaustive lift join over compressed units (independent CPU replay).
   Usage: search n m datadir units.tsv u0 u1 outdir [options]
   Options: --batch B   units per checkpoint file (default 256)
            --threads T (default: all)
            --no-pair   disable the pair spectral filter
            --no-xor    disable the product-theorem (XOR) key
            --no-kmin   disable the kernel-multiplier restriction
            --cap E     max stored entries per pass (default 1<<27)
   For each unit (c1,c2,c3,c4) it chooses a pairing {X,Y}|{Z,W}, enumerates
   every ordered pair of rows on both sides, keeps the pairs passing the
   spectral pair test, stores one side in a hash table keyed by
   (PAF hash, XOR key) and probes with the other; every key match is checked
   exactly on all PAF shifts. One receipt line per unit, written in whole
   batch files (tmp + rename). See the reductions in ../paper/paper.tex for the statements. */
#include "common.h"
#include <omp.h>
#include <time.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>
#ifdef __ARM_NEON
#include <arm_neon.h>
#endif

static params P;
static void *xmalloc(size_t z) { void *p = malloc(z ? z : 1); if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", z); exit(3); } return p; }
static void *xcalloc(size_t a, size_t z) { void *p = calloc(a ? a : 1, z); if (!p) { fprintf(stderr, "out of memory\n"); exit(3); } return p; }
static void *xrealloc(void *q, size_t z) { void *p = realloc(q, z); if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", z); exit(3); } return p; }
static uint32_t *ROWS; static uint64_t NROWS;
static int NCLS; static uint64_t *COFF, *CCNT; static int *CRS;
static uint64_t RH[MAXH + 1];       /* hash multipliers per shift */
static const uint64_t RX = 0xd6e8feb86659fd93ULL; /* XOR-key mixer */
static int KU[64], NKU;             /* kernel multipliers u != 1, u == 1 mod L */
static int OPT_PAIR = 1, OPT_XOR = 1, OPT_KMIN = 1;
static uint64_t CAP = 1ULL << 27;
static int KEYBITS = 64;             /* < 64: truncate keys to force collisions (stress test) */
static int SCALE;                   /* 64 */

typedef struct {        /* per-row data for one class list */
  int N;
  uint32_t *mask;
  uint64_t *h;          /* sum_s PAF(s) RH[s] mod 2^64 */
  uint16_t *lo, *hi;    /* [k*N + j], k = 0..H-1: lo <= 64 lambda^2 <= hi */
  uint16_t minlo[MAXH], maxhi[MAXH];
} rlist;

static double *TLO, *THI; static int HL;    /* half tables for lambda */
static uint32_t KT[64][4][256];              /* byte tables for kernel multipliers */

static void init_fast(void) {
  int H = P.H; HL = H / 2; int h2 = H - HL;
  TLO = malloc(((size_t)1 << HL) * H * sizeof(double));
  THI = malloc(((size_t)1 << h2) * H * sizeof(double));
  for (size_t lo = 0; lo < ((size_t)1 << HL); lo++)
    for (int k = 1; k <= H; k++) {
      double s = 0;
      for (int i = 1; i <= HL; i++) s += (((lo >> (i - 1)) & 1) ? -1.0 : 1.0) * P.cs[(i * k) % P.n];
      TLO[lo * H + (k - 1)] = s;
    }
  for (size_t hi = 0; hi < ((size_t)1 << h2); hi++)
    for (int k = 1; k <= H; k++) {
      double s = 0;
      for (int i = HL + 1; i <= H; i++) s += (((hi >> (i - HL - 1)) & 1) ? -1.0 : 1.0) * P.cs[(i * k) % P.n];
      THI[hi * H + (k - 1)] = s;
    }
  for (int t = 0; t < NKU; t++)
    for (int by = 0; by < 4; by++)
      for (int v = 0; v < 256; v++) {
        uint32_t r = 0;
        /* old bit position q (0-based) = byte*8+b holds x_{q+1}; it moves to every new i with u*i == +-(q+1) */
        for (int b = 0; b < 8; b++) {
          int q = by * 8 + b; if (q >= H || !((v >> b) & 1)) continue;
          for (int i = 1; i <= H; i++) { int p = (KU[t] * i) % P.n; if (p > H) p = P.n - p; if (p == q + 1) r |= 1u << (i - 1); }
        }
        KT[t][by][v] = r;
      }
}
static inline uint32_t kmult(uint32_t mk, int t) {
  return KT[t][0][mk & 255] | KT[t][1][(mk >> 8) & 255] | KT[t][2][(mk >> 16) & 255] | KT[t][3][mk >> 24];
}
/* PAF via a bit vector of the full row (bit i set iff x_i = -1): PAF(s) = n - 2 popcount(v xor rot(v, s)). */
static inline void paf_fast(uint32_t mask, int *paf) {
  int n = P.n; unsigned __int128 v = 0, full = (((unsigned __int128)1) << n) - 1;
  for (int i = 1; i <= P.H; i++) if ((mask >> (i - 1)) & 1) v |= ((unsigned __int128)1 << i) | ((unsigned __int128)1 << (n - i));
  for (int s = 0; s <= P.H; s++) {
    unsigned __int128 r = ((v >> s) | (v << (n - s))) & full, d = v ^ r;
    paf[s] = n - 2 * (__builtin_popcountll((uint64_t)d) + __builtin_popcountll((uint64_t)(d >> 64)));
  }
}

static uint32_t mult_mask(uint32_t mask, int u) {
  uint32_t r = 0;
  for (int i = 1; i <= P.H; i++) {
    int p = (u * i) % P.n; if (p > P.H) p = P.n - p;
    if ((mask >> (p - 1)) & 1) r |= 1u << (i - 1);
  }
  return r;
}

static void build_list(rlist *R, int cls, int kmin) {
  uint64_t off = COFF[cls], cnt = CCNT[cls];
  R->mask = xmalloc((cnt ? cnt : 1) * sizeof(uint32_t));
  int N = 0;
  for (uint64_t i = 0; i < cnt; i++) {
    uint32_t mk = ROWS[off + i];
    if (kmin) { int ok = 1; for (int t = 0; t < NKU; t++) if (kmult(mk, t) < mk) { ok = 0; break; } if (!ok) continue; }
    R->mask[N++] = mk;
  }
  R->N = N; int H = P.H;
  R->h = xmalloc((N ? N : 1) * sizeof(uint64_t));
  R->lo = xmalloc((size_t)(N ? N : 1) * H * sizeof(uint16_t));
  R->hi = xmalloc((size_t)(N ? N : 1) * H * sizeof(uint16_t));
  for (int k = 0; k < H; k++) { R->minlo[k] = 65535; R->maxhi[k] = 0; }
  uint32_t lomask = (1u << HL) - 1;
  for (int j = 0; j < N; j++) {
    int paf[MAXH + 1];
    uint32_t mk = R->mask[j];
    paf_fast(mk, paf);
    uint64_t h = 0; for (int s = 1; s <= H; s++) h += (uint64_t)(int64_t)paf[s] * RH[s];
    R->h[j] = h;
    const double *a = TLO + (size_t)(mk & lomask) * H, *b = THI + (size_t)(mk >> HL) * H;
    for (int k = 1; k <= H; k++) {
      double l = 1.0 + 2.0 * (a[k - 1] + b[k - 1]), q = (double)SCALE * l * l;
      double qa = floor(q - 0.01), qb = ceil(q + 0.01);
      if (qa < 0) qa = 0;
      if (qb > 65535) qb = 65535;
      uint16_t A = (uint16_t)qa, B = (uint16_t)qb;
      R->lo[(size_t)(k - 1) * N + j] = A; R->hi[(size_t)(k - 1) * N + j] = B;
      if (A < R->minlo[k - 1]) R->minlo[k - 1] = A;
      if (B > R->maxhi[k - 1]) R->maxhi[k - 1] = B;
    }
  }
}
/* kernel-minimal restriction of a built list (keeps the per-row data of kernel-minimal rows) */
static void restrict_kmin(rlist *R) {
  int H = P.H, N = R->N, M = 0;
  int *keep = xmalloc((N ? N : 1) * sizeof(int));
  for (int j = 0; j < N; j++) { int ok = 1; for (int t = 0; t < NKU; t++) if (kmult(R->mask[j], t) < R->mask[j]) { ok = 0; break; } if (ok) keep[M++] = j; }
  uint16_t *lo = xmalloc((size_t)(M ? M : 1) * H * sizeof(uint16_t)), *hi = xmalloc((size_t)(M ? M : 1) * H * sizeof(uint16_t));
  for (int k = 0; k < H; k++) {
    R->minlo[k] = 65535; R->maxhi[k] = 0;
    for (int t = 0; t < M; t++) {
      lo[(size_t)k * M + t] = R->lo[(size_t)k * N + keep[t]]; hi[(size_t)k * M + t] = R->hi[(size_t)k * N + keep[t]];
      if (lo[(size_t)k * M + t] < R->minlo[k]) R->minlo[k] = lo[(size_t)k * M + t];
      if (hi[(size_t)k * M + t] > R->maxhi[k]) R->maxhi[k] = hi[(size_t)k * M + t];
    }
  }
  for (int t = 0; t < M; t++) { R->mask[t] = R->mask[keep[t]]; R->h[t] = R->h[keep[t]]; }
  free(R->lo); free(R->hi); R->lo = lo; R->hi = hi; R->N = M; free(keep);
}
static int count_kmin(const rlist *R) {
  int M = 0;
  for (int j = 0; j < R->N; j++) { int ok = 1; for (int t = 0; t < NKU; t++) if (kmult(R->mask[j], t) < R->mask[j]) { ok = 0; break; } M += ok; }
  return M;
}
static void free_list(rlist *R) { free(R->mask); free(R->h); free(R->lo); free(R->hi); }

typedef struct { uint64_t key; uint32_t i, j; } entry;
#define MAXSOL 4096

/* pair keys: left (X,Y): (hX+hY) ^ RX*(mX^mY); right (Z,W): (-(hZ+hW)) ^ RX*(~(mZ^mW)&full).
   Key 0 is reserved for empty table slots and is remapped to 1 on both sides. */
static inline uint64_t pair_key(uint64_t hsum, uint32_t xr) {
  uint64_t k = hsum;
  if (OPT_XOR) k ^= RX * (uint64_t)xr;
  if (KEYBITS < 64) k &= (1ULL << KEYBITS) - 1;
  return k ? k : 1;
}

typedef struct {
  uint16_t U[MAXH], Lb[MAXH]; int ord[MAXH];
} bounds;

/* Bounds for pair (X,Y) given the other side (Z,W):
   64(lX^2+lY^2) = 64*4n - 64(lZ^2+lW^2) in [64*4n - maxhiZ - maxhiW, 64*4n - minloZ - minloW]. */
static void make_bounds(bounds *B, const rlist *Z, const rlist *W) {
  int T = SCALE * 4 * P.n;
  for (int k = 0; k < P.H; k++) {
    int u = T - Z->minlo[k] - W->minlo[k], l = T - Z->maxhi[k] - W->maxhi[k];
    if (l < 0) l = 0;
    if (u < 0) u = 0; /* a negative bound only makes the test looser than exact: still sound */
    B->U[k] = (uint16_t)u; B->Lb[k] = (uint16_t)l; B->ord[k] = k;
  }
}

/* Order frequencies by rejection on a deterministic sample of pairs (first rows). */
static void order_freqs(bounds *B, const rlist *X, const rlist *Y) {
  int H = P.H; long rej[MAXH] = {0};
  int nx = X->N < 64 ? X->N : 64, ny = Y->N < 64 ? Y->N : 64;
  for (int a = 0; a < nx; a++) for (int b = 0; b < ny; b++)
    for (int k = 0; k < H; k++) {
      int s = X->lo[(size_t)k * X->N + a] + Y->lo[(size_t)k * Y->N + b];
      int t = X->hi[(size_t)k * X->N + a] + Y->hi[(size_t)k * Y->N + b];
      if (s > B->U[k] || t < B->Lb[k]) rej[k]++;
    }
  for (int i = 0; i < H; i++) for (int j = i + 1; j < H; j++)
    if (rej[B->ord[j]] > rej[B->ord[i]]) { int t = B->ord[i]; B->ord[i] = B->ord[j]; B->ord[j] = t; }
}

#ifndef F1
#define F1 8
#endif
/* Enumerate all ordered pairs (a in X, b in Y); call emit for survivors. Returns pairs enumerated. */
typedef void (*emit_fn)(void *ctx, int a, int b);
static inline void tail_check(const rlist *X, const rlist *Y, const bounds *B, int a, int b,
                              const uint16_t *lx, const uint16_t *hx, emit_fn emit, void *ctx, uint64_t *ns) {
  int NY = Y->N;
  (void)X;
  for (int t = F1; t < P.H; t++) {
    int k = B->ord[t];
    if ((int)lx[k] + Y->lo[(size_t)k * NY + b] > B->U[k] || (int)hx[k] + Y->hi[(size_t)k * NY + b] < B->Lb[k]) return;
  }
  (*ns)++; emit(ctx, a, b);
}
static uint64_t enum_pairs(const rlist *X, const rlist *Y, const bounds *B, emit_fn emit, void *ctx, uint64_t *surv) {
  int H = P.H, NY = Y->N;
  uint64_t ns = 0;
  for (int a = 0; a < X->N; a++) {
    uint16_t lx[MAXH], hx[MAXH];
    for (int k = 0; k < H; k++) { lx[k] = X->lo[(size_t)k * X->N + a]; hx[k] = X->hi[(size_t)k * X->N + a]; }
    if (OPT_PAIR) {
      int bad = 0;
      const uint16_t *lp[F1], *hp[F1]; uint16_t uu[F1], vv[F1];
      for (int t = 0; t < F1; t++) {
        int k = B->ord[t % H]; /* H < F1 (n < 17): repeat frequencies, a no-op for the test */
        lp[t] = Y->lo + (size_t)k * NY; hp[t] = Y->hi + (size_t)k * NY;
        if (lx[k] > B->U[k]) bad = 1;
        uu[t] = bad ? 0 : B->U[k] - lx[k];
        int g = B->Lb[k] - hx[k]; vv[t] = g > 0 ? g : 0;
      }
      if (bad) continue; /* no partner can pass: lo_b >= 0 */
      int b = 0;
#ifdef __ARM_NEON
      uint16x8_t U8[F1], V8[F1];
      for (int t = 0; t < F1; t++) { U8[t] = vdupq_n_u16(uu[t]); V8[t] = vdupq_n_u16(vv[t]); }
      for (; b + 8 <= NY; b += 8) {
        uint16x8_t acc = vandq_u16(vcleq_u16(vld1q_u16(lp[0] + b), U8[0]), vcgeq_u16(vld1q_u16(hp[0] + b), V8[0]));
        for (int t = 1; t < F1; t++)
          acc = vandq_u16(acc, vandq_u16(vcleq_u16(vld1q_u16(lp[t] + b), U8[t]), vcgeq_u16(vld1q_u16(hp[t] + b), V8[t])));
        if (!vmaxvq_u16(acc)) continue;
        uint16_t lanes[8]; vst1q_u16(lanes, acc);
        for (int e = 0; e < 8; e++) if (lanes[e]) tail_check(X, Y, B, a, b + e, lx, hx, emit, ctx, &ns);
      }
#endif
      for (; b < NY; b++) {
        int pass = 1;
        for (int t = 0; t < F1; t++) if (!(lp[t][b] <= uu[t] && hp[t][b] >= vv[t])) { pass = 0; break; }
        if (pass) tail_check(X, Y, B, a, b, lx, hx, emit, ctx, &ns);
      }
    } else {
      for (int b = 0; b < NY; b++) { ns++; emit(ctx, a, b); }
    }
  }
  *surv = ns;
  return (uint64_t)X->N * (uint64_t)NY;
}

typedef struct {
  const rlist *X, *Y; int right; int npass, pass; int nbits;
  entry *buf; uint64_t nbuf, cap; int overflow;
  entry *tab; uint64_t tmask;
  const rlist *Z, *W;  /* the stored side when probing */
  uint64_t matches, sols; uint32_t (*solbuf)[4]; int nsolbuf; int unit; int rowpos[4];
  uint64_t passsurv;
} jctx;

static inline uint64_t key_of(const jctx *c, int a, int b) {
  uint32_t full = P.H == 32 ? 0xffffffffu : ((1u << P.H) - 1);
  uint32_t ma = c->X->mask[a], mb = c->Y->mask[b];
  if (!c->right) return pair_key(c->X->h[a] + c->Y->h[b], ma ^ mb);
  return pair_key((uint64_t)0 - (c->X->h[a] + c->Y->h[b]), ~(ma ^ mb) & full);
}
static inline int in_pass(const jctx *c, uint64_t k) {
  return c->npass == 1 || (int)(k >> (64 - c->nbits)) == c->pass;
}
static void emit_store(void *v, int a, int b) {
  jctx *c = v; uint64_t k = key_of(c, a, b);
  if (!in_pass(c, k)) return;
  c->passsurv++;
  if (c->nbuf >= c->cap) {
    if (c->cap >= CAP) { c->overflow = 1; return; }
    c->cap = c->cap * 2 < CAP ? c->cap * 2 : CAP;
    c->buf = xrealloc(c->buf, c->cap * sizeof(entry));
  }
  c->buf[c->nbuf++] = (entry){k, (uint32_t)a, (uint32_t)b};
}

static int exact_check(const uint32_t *m4) {
  int tot[MAXH + 1] = {0};
  for (int r = 0; r < 4; r++) { int paf[MAXH + 1]; paf_of_mask(&P, m4[r], paf); for (int s = 0; s <= P.H; s++) tot[s] += paf[s]; }
  if (tot[0] != 4 * P.n) return 0;
  for (int s = 1; s <= P.H; s++) if (tot[s]) return 0;
  return 1;
}

static void emit_probe(void *v, int a, int b) {
  jctx *c = v; uint64_t k = key_of(c, a, b);
  if (!in_pass(c, k)) return;
  c->passsurv++;
  uint64_t s = (k * 0x9e3779b97f4a7c15ULL) >> 1;
  for (uint64_t i = s & c->tmask;; i = (i + 1) & c->tmask) {
    entry *e = &c->tab[i];
    if (!e->key) break;
    if (e->key != k) continue;
    c->matches++;
    /* rows in pairing order: probe pair (X,Y) = positions rowpos[0],rowpos[1]; stored (Z,W) = rowpos[2],rowpos[3] */
    uint32_t q[4] = {c->X->mask[a], c->Y->mask[b], c->Z->mask[e->i], c->W->mask[e->j]};
    if (exact_check(q)) {
      uint32_t o[4];
      for (int r = 0; r < 4; r++) o[c->rowpos[r]] = q[r];
      if (c->nsolbuf < MAXSOL) memcpy(c->solbuf[c->nsolbuf++], o, sizeof o);
      c->sols++;
    }
  }
}

typedef struct {
  int unit, cls[4], pairing, desig, sizes[4], npass;
  uint64_t pairs_store, pairs_probe, surv_store, surv_probe, matches, sols; int sols_truncated;
  double cpu;
} receipt;

static const int PAIRS[3][4] = {{0, 1, 2, 3}, {0, 2, 1, 3}, {0, 3, 1, 2}};

static void do_unit(int unit, const int *cls, receipt *R, FILE *solf) {
  struct timespec ts0; clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts0);
  memset(R, 0, sizeof *R);
  R->unit = unit; memcpy(R->cls, cls, sizeof R->cls);
  /* choose pairing and designated row from class counts and kernel-min counts */
  double best = 1e300; int bp = 0, bd = -1;
  rlist L[4]; int km[4];
  for (int r = 0; r < 4; r++) { build_list(&L[r], cls[r], 0); km[r] = OPT_KMIN ? count_kmin(&L[r]) : L[r].N; }
  for (int p = 0; p < 3; p++) for (int d = (OPT_KMIN ? 0 : -1); d < (OPT_KMIN ? 4 : 0); d++) {
    double s[4]; for (int r = 0; r < 4; r++) s[r] = (double)L[r].N;
    if (d >= 0) s[d] = (double)km[d];
    const int *q = PAIRS[p];
    double c = s[q[0]] * s[q[1]] + s[q[2]] * s[q[3]];
    if (c < best) { best = c; bp = p; bd = d; }
  }
  if (bd >= 0) restrict_kmin(&L[bd]);
  R->pairing = bp; R->desig = bd;
  for (int r = 0; r < 4; r++) R->sizes[r] = L[r].N;
  const int *q = PAIRS[bp];
  /* store the side with fewer pairs; probe with the other. Left pair = (q0,q1), right = (q2,q3). */
  uint64_t pl = (uint64_t)L[q[0]].N * L[q[1]].N, pr = (uint64_t)L[q[2]].N * L[q[3]].N;
  int store_right = pr <= pl;
  int sp[2] = {store_right ? q[2] : q[0], store_right ? q[3] : q[1]};
  int pp[2] = {store_right ? q[0] : q[2], store_right ? q[1] : q[3]};
  const rlist *SX = &L[sp[0]], *SY = &L[sp[1]], *PX = &L[pp[0]], *PY = &L[pp[1]];
  bounds Bs, Bp;
  make_bounds(&Bs, PX, PY); make_bounds(&Bp, SX, SY);
  order_freqs(&Bs, SX, SY); order_freqs(&Bp, PX, PY);
  int npass = 1, nbits = 0;
  uint32_t (*solbuf)[4] = xmalloc(MAXSOL * sizeof *solbuf); int nsol = 0;
  for (;;) {
    nsol = 0; /* an attempt abandoned for capacity reports nothing */
    uint64_t ss = 0, sp2 = 0, mt = 0, so = 0, pst = 0, ppr = 0; int fail = 0;
    for (int pass = 0; pass < npass && !fail; pass++) {
      jctx c; memset(&c, 0, sizeof c);
      c.X = SX; c.Y = SY; c.right = store_right; c.npass = npass; c.pass = pass; c.nbits = nbits;
      c.cap = 1024; c.buf = xmalloc(c.cap * sizeof(entry));
      uint64_t sv; pst = enum_pairs(SX, SY, &Bs, emit_store, &c, &sv);
      if (c.overflow) { free(c.buf); fail = 1; break; }
      ss += c.passsurv;
      uint64_t tsz = 2; while (tsz < 2 * c.nbuf + 2) tsz <<= 1;
      c.tab = xcalloc(tsz, sizeof(entry)); c.tmask = tsz - 1;
      for (uint64_t i = 0; i < c.nbuf; i++) {
        entry e = c.buf[i];
        uint64_t s = (e.key * 0x9e3779b97f4a7c15ULL) >> 1;
        uint64_t j = s & c.tmask;
        while (c.tab[j].key) j = (j + 1) & c.tmask;
        c.tab[j] = e;
      }
      free(c.buf); c.buf = NULL;
      jctx d = c;
      d.X = PX; d.Y = PY; d.right = !store_right; d.Z = SX; d.W = SY; d.passsurv = 0;
      d.solbuf = solbuf; d.nsolbuf = nsol; d.unit = unit;
      d.rowpos[0] = pp[0]; d.rowpos[1] = pp[1]; d.rowpos[2] = sp[0]; d.rowpos[3] = sp[1];
      ppr = enum_pairs(PX, PY, &Bp, emit_probe, &d, &sv);
      sp2 += d.passsurv; mt += d.matches; so += d.sols; nsol = d.nsolbuf;
      free(c.tab);
    }
    if (fail) { npass *= 2; nbits++; continue; }
    R->pairs_store = pst; R->pairs_probe = ppr; R->surv_store = ss; R->surv_probe = sp2;
    R->matches = mt; R->sols = so; R->npass = npass;
    break;
  }
  if (nsol) {
#pragma omp critical
    {
      for (int i = 0; i < nsol; i++) fprintf(solf, "SOLUTION\t%d\t%u\t%u\t%u\t%u\n", unit, solbuf[i][0], solbuf[i][1], solbuf[i][2], solbuf[i][3]);
      fflush(solf);
    }
  }
  if (R->sols > (uint64_t)MAXSOL) R->sols_truncated = 1;
  free(solbuf);
  for (int r = 0; r < 4; r++) free_list(&L[r]);
  struct timespec ts1; clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts1);
  R->cpu = (double)(ts1.tv_sec - ts0.tv_sec) + 1e-9 * (double)(ts1.tv_nsec - ts0.tv_nsec); /* this thread's CPU time */
}

static int load_tsv_classes(const char *path) {
  FILE *f = fopen(path, "r"); if (!f) return -1;
  char line[4096]; int n = 0, cap = 1024;
  COFF = malloc(cap * sizeof(uint64_t)); CCNT = malloc(cap * sizeof(uint64_t)); CRS = malloc(cap * sizeof(int));
  while (fgets(line, sizeof line, f)) {
    int id, rs; unsigned key; char xs[1024]; unsigned long long c, o;
    if (sscanf(line, "%d\t%u\t%d\t%1023s\t%llu\t%llu", &id, &key, &rs, xs, &c, &o) != 6 || id != n) return -1;
    if (n == cap) { cap *= 2; COFF = realloc(COFF, cap * sizeof(uint64_t)); CCNT = realloc(CCNT, cap * sizeof(uint64_t)); CRS = realloc(CRS, cap * sizeof(int)); }
    COFF[n] = o; CCNT[n] = c; CRS[n] = rs; n++;
  }
  fclose(f); NCLS = n; return 0;
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: search n m datadir units.tsv u0 u1 outdir [opts]\n"); return 2; }
  int n = atoi(argv[1]), m = atoi(argv[2]);
  const char *dd = argv[3], *uf = argv[4], *od = argv[7];
  int u0 = atoi(argv[5]), u1 = atoi(argv[6]), batch = 256, threads = 0;
  for (int i = 8; i < argc; i++) {
    if (!strcmp(argv[i], "--batch")) batch = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--no-pair")) OPT_PAIR = 0;
    else if (!strcmp(argv[i], "--no-xor")) OPT_XOR = 0;
    else if (!strcmp(argv[i], "--no-kmin")) OPT_KMIN = 0;
    else if (!strcmp(argv[i], "--cap")) CAP = strtoull(argv[++i], 0, 0);
    else if (!strcmp(argv[i], "--keybits")) KEYBITS = atoi(argv[++i]);
    else { fprintf(stderr, "bad option %s\n", argv[i]); return 2; }
  }
  if (threads > 0) omp_set_num_threads(threads);
  params_init(&P, n, m); SCALE = 64;
  if (SCALE * 4 * n * 2 + 8 > 65535) { fprintf(stderr, "n too large for uint16 scale\n"); return 2; }
  uint64_t st = 0x5713a1d2c0ffee65ULL; for (int s = 0; s <= MAXH; s++) RH[s] = splitmix64(&st) | 1;
  NKU = 0; for (int u = 2; u < n; u++) { int a = u, b = n; while (b) { int t = a % b; a = b; b = t; } if (a == 1 && u % P.L == 1) KU[NKU++] = u; }
  char path[4096];
  snprintf(path, sizeof path, "%s/classes.tsv", dd);
  if (load_tsv_classes(path)) { fprintf(stderr, "bad classes\n"); return 1; }
  snprintf(path, sizeof path, "%s/rows.bin", dd);
  FILE *f = fopen(path, "rb"); if (!f) { fprintf(stderr, "no rows\n"); return 1; }
  fseek(f, 0, SEEK_END); NROWS = (uint64_t)ftell(f) / 4; fseek(f, 0, SEEK_SET);
  ROWS = malloc(NROWS * 4 + 4);
  if (fread(ROWS, 4, NROWS, f) != NROWS) { fprintf(stderr, "short rows\n"); return 1; }
  fclose(f);
  init_fast();
  if (COFF[NCLS - 1] + CCNT[NCLS - 1] != NROWS) { fprintf(stderr, "rows/classes mismatch\n"); return 1; }
  /* units */
  f = fopen(uf, "r"); if (!f) return 1;
  int nu = 0, capu = 1024; int (*U)[4] = malloc(capu * sizeof *U);
  char line[1024];
  while (fgets(line, sizeof line, f)) {
    int id, a, b, c, d, o;
    if (sscanf(line, "%d\t%d\t%d\t%d\t%d\t%d", &id, &a, &b, &c, &d, &o) != 6 || id != nu) { fprintf(stderr, "bad units\n"); return 1; }
    if (nu == capu) { capu *= 2; U = realloc(U, capu * sizeof *U); }
    U[nu][0] = a; U[nu][1] = b; U[nu][2] = c; U[nu][3] = d; nu++;
  }
  fclose(f);
  if (u1 > nu) u1 = nu;
  mkdir(od, 0755);
  snprintf(path, sizeof path, "%s/solutions.tsv", od);
  FILE *solf = fopen(path, "a");
  for (int b0 = u0; b0 < u1; b0 += batch) {
    int b1 = b0 + batch < u1 ? b0 + batch : u1;
    char fin[4096], tmp[4096];
    snprintf(fin, sizeof fin, "%s/batch_%06d_%06d.tsv", od, b0, b1);
    if (access(fin, F_OK) == 0) continue; /* completed batch: checkpoint */
    receipt *RS = calloc(b1 - b0, sizeof(receipt));
    double w0 = omp_get_wtime();
#pragma omp parallel for schedule(dynamic, 1)
    for (int u = b0; u < b1; u++) do_unit(u, U[u], &RS[u - b0], solf);
    snprintf(tmp, sizeof tmp, "%s.tmp", fin);
    FILE *g = fopen(tmp, "w");
    double cpu = 0;
    for (int u = b0; u < b1; u++) {
      receipt *R = &RS[u - b0]; cpu += R->cpu;
      fprintf(g, "U\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%.3f\n",
              R->unit, R->cls[0], R->cls[1], R->cls[2], R->cls[3], R->pairing, R->desig,
              R->sizes[0], R->sizes[1], R->sizes[2], R->sizes[3], R->npass,
              (unsigned long long)R->pairs_store, (unsigned long long)R->pairs_probe,
              (unsigned long long)R->surv_store, (unsigned long long)R->surv_probe,
              (unsigned long long)R->matches, (unsigned long long)R->sols, R->cpu);
    }
    fprintf(g, "END\t%d\t%d\t%.3f\t%.3f\tpair=%d xor=%d kmin=%d keybits=%d cap=%llu\n", b0, b1, cpu, omp_get_wtime() - w0, OPT_PAIR, OPT_XOR, OPT_KMIN, KEYBITS, (unsigned long long)CAP);
    fflush(g); fsync(fileno(g)); fclose(g);
    if (getenv("W_TEST_PAUSE_BEFORE_RENAME")) sleep((unsigned)atoi(getenv("W_TEST_PAUSE_BEFORE_RENAME"))); /* rehearsal hook: kill window */
    if (rename(tmp, fin)) { perror("rename"); return 1; }
    free(RS);
  }
  fclose(solf);
  return 0;
}
