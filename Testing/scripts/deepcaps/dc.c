/* Deep-caps measurement tool (bench only, not part of the proved aligner).
   dc truth <genome.fa> <names.fq> <mates.txt>   per mate: index pen nmis ngapev coords   (coords: errReps-style
       2i+1 mismatch / inserted read letter i, 2i deletion before letter i; glocal affine DP at the true locus
       ±SLACK, scoring 0/-4/-6/-2; mates.txt = WG_TRIMOUT text: '>r{i}' / sequence, empty = trimmed away)
   dc kmer <genome.fa> <mates.txt> <npairs-mates> L1,L2,..   per L: hits (both strands) of each disjoint L-seed
       of the first n mates (seed j at j*(n/m), m = n/L): prints one line per seed: L mate j hits
   Fails hard (assert) on anything unexpected. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SLACK 40
static char *G; static size_t GN; static int NC; static char *CN[1024]; static size_t CO[1024], CL[1024];
static void load_genome(const char *p) {
  FILE *f = fopen(p, "rb"); assert(f); fseek(f, 0, SEEK_END); size_t sz = ftell(f); fseek(f, 0, SEEK_SET);
  G = malloc(sz); assert(G); char *line = malloc(1 << 20); size_t n = 0;
  while (fgets(line, 1 << 20, f)) {
    size_t l = strlen(line); while (l && (line[l-1] == '\n' || line[l-1] == '\r')) line[--l] = 0;
    if (line[0] == '>') { if (NC) CL[NC-1] = n - CO[NC-1]; assert(NC < 1024);
      char *s = line + 1; char *sp = strpbrk(s, " \t"); if (sp) *sp = 0; CN[NC] = strdup(s); CO[NC] = n; NC++; continue; }
    for (size_t i = 0; i < l; i++) { char c = line[i]; if (c >= 'a') c -= 32; G[n++] = c; }
  }
  CL[NC-1] = n - CO[NC-1]; GN = n; fclose(f); free(line);
  fprintf(stderr, "genome %zu letters, %d records\n", GN, NC);
}
static int chrom(const char *s) { for (int i = 0; i < NC; i++) if (!strcmp(CN[i], s)) return i; assert(0); return -1; }
static char comp(char c) { switch (c) { case 'A': return 'T'; case 'C': return 'G'; case 'G': return 'C'; case 'T': return 'A'; } return 'N'; }
/* read mates text: returns array of strings (NULL = trimmed away) */
static char **read_mates(const char *p, int *cnt) {
  FILE *f = fopen(p, "r"); assert(f); int cap = 1 << 20, n = 0; char **a = malloc(sizeof(char*) * cap);
  char *line = malloc(1 << 16);
  while (fgets(line, 1 << 16, f)) {
    assert(line[0] == '>'); char *s = malloc(1 << 14); assert(fgets(s, 1 << 14, f));
    size_t l = strlen(s); while (l && (s[l-1] == '\n')) s[--l] = 0;
    if (n == cap) { cap *= 2; a = realloc(a, sizeof(char*) * cap); }
    a[n++] = l ? s : (free(s), NULL);
  }
  fclose(f); free(line); *cnt = n; return a;
}
/* glocal Gotoh: read r[0..n) fully, genome w[0..m) free ends. Minimise cost. Traceback -> coords. */
#define INF 1000000
static int *Mm, *Xx, *Yy; /* (n+1)*(m+1) */
static int align(const char *r, int n, const char *w, int m, int *coords, int *nc, int *nmis, int *ngap) {
  int W = m + 1;
  #define I(i,j) ((size_t)(i)*W+(j))
  for (int j = 0; j <= m; j++) { Mm[I(0,j)] = 0; Xx[I(0,j)] = INF; Yy[I(0,j)] = INF; }
  for (int i = 1; i <= n; i++) {
    Mm[I(i,0)] = INF; Xx[I(i,0)] = INF; Yy[I(i,0)] = 6 + 2 * i;
    for (int j = 1; j <= m; j++) {
      int s = (r[i-1] == w[j-1] && r[i-1] != 'N') ? 0 : 4;
      int b = Mm[I(i-1,j-1)]; if (Xx[I(i-1,j-1)] < b) b = Xx[I(i-1,j-1)]; if (Yy[I(i-1,j-1)] < b) b = Yy[I(i-1,j-1)];
      Mm[I(i,j)] = b + s;
      /* X: deletion (genome letter j consumed, read stays at i) */
      int x = Mm[I(i,j-1)] + 8; if (Yy[I(i,j-1)] + 8 < x) x = Yy[I(i,j-1)] + 8; if (Xx[I(i,j-1)] + 2 < x) x = Xx[I(i,j-1)] + 2;
      Xx[I(i,j)] = x;
      /* Y: insertion (read letter i consumed) */
      int y = Mm[I(i-1,j)] + 8; if (Xx[I(i-1,j)] + 8 < y) y = Xx[I(i-1,j)] + 8; if (Yy[I(i-1,j)] + 2 < y) y = Yy[I(i-1,j)] + 2;
      Yy[I(i,j)] = y;
    }
  }
  int best = INF, bj = 0, bs = 0;
  for (int j = 0; j <= m; j++) { if (Mm[I(n,j)] < best) { best = Mm[I(n,j)]; bj = j; bs = 0; }
    if (Yy[I(n,j)] < best) { best = Yy[I(n,j)]; bj = j; bs = 2; } }
  /* traceback */
  int i = n, j = bj, st = bs; *nc = 0; *nmis = 0; *ngap = 0;
  while (i > 0) {
    if (st == 0) {
      int s = (r[i-1] == w[j-1] && r[i-1] != 'N') ? 0 : 4; int prev = Mm[I(i,j)] - s;
      if (s) { coords[(*nc)++] = 2 * (i - 1) + 1; (*nmis)++; }
      i--; j--;
      if (i == 0) break;
      if (Mm[I(i,j)] == prev) st = 0; else if (Xx[I(i,j)] == prev) st = 1; else { assert(Yy[I(i,j)] == prev); st = 2; }
    } else if (st == 1) {
      int v = Xx[I(i,j)]; j--;
      if (Xx[I(i,j)] + 2 == v) st = 1;
      else { coords[(*nc)++] = 2 * i; (*ngap)++; if (Mm[I(i,j)] + 8 == v) st = 0; else { assert(Yy[I(i,j)] + 8 == v); st = 2; } }
    } else {
      int v = Yy[I(i,j)]; coords[(*nc)++] = 2 * (i - 1) + 1; i--;
      if (i == 0) { (*ngap)++; break; }
      if (Yy[I(i,j)] + 2 == v) st = 2;
      else { (*ngap)++; if (Mm[I(i,j)] + 8 == v) st = 0; else { assert(Xx[I(i,j)] + 8 == v); st = 1; } }
    }
  }
  return best;
}
static int cmpi(const void *a, const void *b) { return *(int*)a - *(int*)b; }
static void truth(char **argv) {
  load_genome(argv[2]);
  int nm; char **ms = read_mates(argv[4], &nm);
  FILE *f = fopen(argv[3], "r"); assert(f); char line[1 << 14]; int k = 0, pair = 0;
  Mm = malloc(sizeof(int) * 2048 * 2400); Xx = malloc(sizeof(int) * 2048 * 2400); Yy = malloc(sizeof(int) * 2048 * 2400);
  int coords[8192];
  int mate = strstr(argv[3], "R2") ? 1 : 0;
  while (fgets(line, sizeof line, f)) {
    if (k++ % 4) continue;
    /* @sN:chr:a-b±:c-d± ; field 1 = this file's mate? R1 file: first interval is mate 1 */
    char nm1[256], c[64]; long a0, a1, b0, b1; char s1, s2;
    assert(sscanf(line, "@%255[^:]:%63[^:]:%ld-%ld%c:%ld-%ld%c", nm1, c, &a0, &a1, &s1, &b0, &b1, &s2) == 8);
    long x0 = mate ? b0 : a0, x1 = mate ? b1 : a1; char sx = mate ? s2 : s1;
    assert(pair < nm);
    char *r = ms[pair];
    if (!r) { printf("%d\t-\n", pair); pair++; continue; }
    int n = strlen(r); assert(n < 2000);
    char rr[2048];
    if (sx == '-') { for (int i = 0; i < n; i++) rr[i] = comp(r[n-1-i]); } else memcpy(rr, r, n);
    int ci = chrom(c); long w0 = x0 - SLACK; if (w0 < 0) w0 = 0; long w1 = x1 + SLACK; if (w1 > (long)CL[ci]) w1 = CL[ci];
    int m = w1 - w0; assert(m > 0 && m < 2400);
    int nc, nmis, ngap; int pen = align(rr, n, G + CO[ci] + w0, m, coords, &nc, &nmis, &ngap);
    /* coords stay in the aligned orientation: a '-' mate is mapped (and seeded) as its reverse complement */
    qsort(coords, nc, sizeof(int), cmpi);
    printf("%d\t%d\t%d\t%d\t%d\t", pair, n, pen, nmis, ngap);
    for (int i = 0; i < nc; i++) printf(i ? ",%d" : "%d", coords[i]);
    printf("\n"); pair++;
  }
  assert(pair == nm);
}
/* ---- kmer hits ---- */
static int code(char c) { switch (c) { case 'A': return 0; case 'C': return 1; case 'G': return 2; case 'T': return 3; } return -1; }
typedef struct { uint64_t *key; uint32_t *cnt; size_t mask; } HT;
static void ht_init(HT *h, size_t n) { size_t s = 1; while (s < 4 * n) s <<= 1; h->mask = s - 1;
  h->key = malloc(8 * s); h->cnt = calloc(s, 4); memset(h->key, 0xff, 8 * s); }
static size_t hh(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; return x; }
static uint32_t *ht_get(HT *h, uint64_t k, int ins) {
  size_t i = hh(k) & h->mask;
  while (h->key[i] != ~0ULL) { if (h->key[i] == k) return &h->cnt[i]; i = (i + 1) & h->mask; }
  if (!ins) return NULL; h->key[i] = k; return &h->cnt[i];
}
static uint64_t rcw(uint64_t x, int L) { uint64_t y = 0; for (int i = 0; i < L; i++) { y = (y << 2) | (3 - (x & 3)); x >>= 2; } return y; }
static void kmer(char **argv) {
  load_genome(argv[2]);
  int nm; char **ms = read_mates(argv[3], &nm); int lim = atoi(argv[4]); if (lim > nm) lim = nm;
  int Ls[16], nL = 0; char *t = strtok(argv[5], ","); while (t) { Ls[nL++] = atoi(t); t = strtok(NULL, ","); }
  HT h[16]; uint64_t **seedk = malloc(sizeof(void*) * 16);
  for (int q = 0; q < nL; q++) {
    int L = Ls[q]; assert(L >= 8 && L <= 32); ht_init(&h[q], (size_t)lim * 64); seedk[q] = malloc(8 * (size_t)lim * 64);
    for (int r = 0; r < lim; r++) {
      char *s = ms[r]; int n = s ? strlen(s) : 0; int m = n / L; assert(m < 64);
      for (int j = 0; j < 64; j++) seedk[q][(size_t)r * 64 + j] = ~0ULL;
      for (int j = 0; j < m; j++) { int st = j * (n / m); uint64_t x = 0; int ok = 1;
        for (int i = 0; i < L; i++) { int c = code(s[st + i]); if (c < 0) { ok = 0; break; } x = (x << 2) | c; }
        if (!ok) continue; uint64_t y = rcw(x, L); uint64_t cn = x < y ? x : y;
        seedk[q][(size_t)r * 64 + j] = cn; ht_get(&h[q], cn, 1); }
    }
  }
  for (int q = 0; q < nL; q++) {
    int L = Ls[q]; uint64_t msk = L == 32 ? ~0ULL : ((1ULL << (2 * L)) - 1); uint64_t f = 0, rv = 0; int run = 0;
    for (size_t p = 0; p < GN; p++) {
      int c = code(G[p]); if (c < 0) { run = 0; f = rv = 0; continue; }
      f = ((f << 2) | c) & msk; rv = (rv >> 2) | ((uint64_t)(3 - c) << (2 * (L - 1))); run++;
      if (run >= L) { uint64_t cn = f < rv ? f : rv; uint32_t *e = ht_get(&h[q], cn, 0); if (e) (*e)++; }
    }
    fprintf(stderr, "L=%d scanned\n", L);
    for (int r = 0; r < lim; r++) for (int j = 0; j < 64; j++) { uint64_t k = seedk[q][(size_t)r * 64 + j];
      if (k == ~0ULL) continue; printf("%d\t%d\t%d\t%u\n", L, r, j, *ht_get(&h[q], k, 0)); }
  }
}
int main(int argc, char **argv) {
  assert(argc >= 2);
  if (!strcmp(argv[1], "truth")) { assert(argc == 5); truth(argv); }
  else if (!strcmp(argv[1], "kmer")) { assert(argc == 6); kmer(argv); }
  else assert(0);
  return 0;
}
