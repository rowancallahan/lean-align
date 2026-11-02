/* Benchmark only (n31 danger regions). Memory-light version of dup_mask.py for whole genomes:
   cc -O2 -o dup_mask Testing/benches/dup_mask.c && ./dup_mask genome.fa [L=150] [out.mask] [parts=16]
   Marks (1 byte per letter, records concatenated, upper-cased) every letter inside a length-L window whose
   canonical (min of forward / reverse-complement) 64-bit hash occurs on >= 2 windows (a copy on either
   strand counts; windows with non-ACGT are ignored). A palindromic window counts once, as in the python tool.
   RAM ~ genome + mask + 8*windows/parts bytes. Hash collisions only over-mark (not a proof input). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
typedef uint64_t u64;
static const u64 B = 1000003ULL;
static u64 mix(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; return x ^ (x >> 33); }
static int cmp(const void *a, const void *b) { u64 x = *(u64 *)a, y = *(u64 *)b; return x < y ? -1 : x > y; }
static unsigned char *g; static size_t n; static int L;
static u64 BL, BINV, BL1;
/* walk all windows of one record; f(i, canon hash, palindrome) */
typedef void (*cb)(size_t i, u64 c, int pal, void *ctx);
static void walk(size_t s, size_t e, cb f, void *ctx) {
  u64 h = 0, r = 0; int run = 0; /* run = consecutive ACGT letters ending at the window end */
  for (size_t k = s; k < e; k++) {
    unsigned c = g[k]; /* 1..4 ACGT, 0 other */
    if (!c) { run = 0; h = r = 0; continue; }
    if (run < L) { /* build */
      h = h * B + c;
      run++;
      if (run == L) { /* compute r directly */
        r = 0; u64 p = 1;
        for (int j = 0; j < L; j++) { r += (u64)(5 - g[k - L + 1 + j]) * p; p *= B; }
        u64 cn = h < r ? h : r; f(k - L + 1, cn, h == r, ctx);
      }
      continue;
    }
    unsigned o = g[k - L];
    h = h * B + c - (u64)o * BL;
    r = (r - (u64)(5 - o)) * BINV + (u64)(5 - c) * BL1;
    u64 cn = h < r ? h : r; f(k - L + 1, cn, h == r, ctx);
  }
}
typedef struct { u64 *a; size_t m; int part, parts; } C1;
static void collect(size_t i, u64 c, int pal, void *x) { (void)i; (void)pal; C1 *t = x; u64 m = mix(c); if ((int)(m % t->parts) == t->part) t->a[t->m++] = m; }
typedef struct { u64 *d; size_t nd; unsigned char *mask; int part, parts; size_t cov; } C2;
static int has(u64 *d, size_t nd, u64 v) { size_t lo = 0, hi = nd; while (lo < hi) { size_t m = (lo + hi) / 2; if (d[m] < v) lo = m + 1; else hi = m; } return lo < nd && d[lo] == v; }
static void markw(size_t i, u64 c, int pal, void *x) {
  (void)pal; C2 *t = x; u64 m = mix(c);
  if ((int)(m % t->parts) == t->part && has(t->d, t->nd, m)) { unsigned char *p = t->mask + i; /* start marks; expanded later */ *p = 1; }
}
int main(int argc, char **argv) {
  assert(argc >= 2); L = argc > 2 ? atoi(argv[2]) : 150; int parts = argc > 4 ? atoi(argv[4]) : 16;
  BL = 1; for (int i = 0; i < L; i++) BL *= B; BL1 = BL / B; /* B^(L-1) */
  { u64 x = 1; for (int i = 0; i < L - 1; i++) x *= B; BL1 = x; }
  BINV = 1; for (int i = 0; i < 7; i++) BINV *= 2 - B * BINV; assert(B * BINV == 1);
  FILE *fp = fopen(argv[1], "rb"); assert(fp);
  fseek(fp, 0, SEEK_END); long fs = ftell(fp); rewind(fp);
  g = malloc(fs); size_t cap = 16; size_t *rs = malloc(cap * 8), *re = malloc(cap * 8); size_t nr = 0; n = 0; int inhdr = 0, bol = 1;
  static const unsigned char lut[256] = {['A'] = 1, ['C'] = 2, ['G'] = 3, ['T'] = 4, ['a'] = 1, ['c'] = 2, ['g'] = 3, ['t'] = 4};
  char *buf = malloc(1 << 20); size_t got;
  while ((got = fread(buf, 1, 1 << 20, fp))) for (size_t k = 0; k < got; k++) {
    unsigned char ch = buf[k];
    if (inhdr) { if (ch == '\n') { inhdr = 0; bol = 1; } continue; }
    if (bol && ch == '>') { if (nr) re[nr - 1] = n; if (nr == cap) { cap *= 2; rs = realloc(rs, cap * 8); re = realloc(re, cap * 8); } rs[nr++] = n; inhdr = 1; continue; }
    bol = 0; if (ch == '\n') { bol = 1; continue; } if (ch == '\r') continue;
    g[n++] = lut[ch];
  }
  re[nr - 1] = n; fclose(fp); free(buf);
  fprintf(stderr, "%zu letters, %zu records\n", n, nr);
  unsigned char *mask = calloc(n + 1, 1); assert(mask);
  size_t nw = 0;
  for (int p = 0; p < parts; p++) {
    size_t cnt = 0; /* upper bound: all windows / parts * 1.2 + slack, grown by realloc */
    size_t capa = n / parts + n / parts / 4 + 1000; u64 *a = malloc(capa * 8); assert(a);
    C1 c1 = {a, 0, p, parts};
    for (size_t r = 0; r < nr; r++) {
      if (re[r] - rs[r] < (size_t)L) continue;
      /* collect may overflow capa only if hash is badly skewed; assert */
      walk(rs[r], re[r], collect, &c1); assert(c1.m <= capa);
    }
    qsort(a, c1.m, 8, cmp);
    size_t nd = 0; for (size_t i = 0; i < c1.m;) { size_t j = i; while (j < c1.m && a[j] == a[i]) j++; if (j - i >= 2) a[nd++] = a[i]; i = j; }
    nw += c1.m; (void)cnt;
    C2 c2 = {a, nd, mask, p, parts, 0};
    for (size_t r = 0; r < nr; r++) if (re[r] - rs[r] >= (size_t)L) walk(rs[r], re[r], markw, &c2);
    fprintf(stderr, "part %d: %zu windows, %zu duplicated hashes\n", p, c1.m, nd); free(a);
  }
  /* mask currently holds window starts; expand to covered letters per record */
  size_t cov = 0;
  for (size_t r = 0; r < nr; r++) { size_t last = 0; /* exclusive end of covered range */
    for (size_t i = rs[r]; i < re[r]; i++) {
      if (mask[i] == 1) { size_t e = i + L; if (e > last) last = e; }
      mask[i] = i < last; cov += mask[i]; } }
  printf("L=%d genome %zu bases (%zu windows), inside an exact duplicated L-mer: %zu (%.2f%%)\n", L, n, nw, cov, 100.0 * cov / n);
  if (argc > 3) { FILE *o = fopen(argv[3], "wb"); fwrite(mask, 1, n, o); fclose(o); }
  return 0;
}
