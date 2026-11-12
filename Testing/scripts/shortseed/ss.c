// Short-seed prototype (unproved, measurement only).
// ss GENOME.fa K W MAXOCC CAP set1_1.fq set1_2.fq [set2_1.fq set2_2.fq ...]
// Index: forward-strand (K,W) minimizers of the genome, CSR by the top 28 bits of the hash.
// Per mate and strand: read minimizers -> exact hits (verified on the genome; buckets with more than
// MAXOCC exact hits skipped, 0 = no limit) -> diagonals -> banded affine DP (mismatch 4, open 6, extend 2,
// semi-global: whole read, free genome ends) -> placements with penalty <= CAP.
// Pairs: mate 1 x mate 2 placements, same chromosome, opposite strands, FR, fragment 100..1000.
// Output per set: pairs with a proper pair, unique best, at truth (sim names), penalty histogram, hits.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <time.h>

#define BB 28
static uint8_t *G;          // genome codes 0..3, 4 = other
static uint64_t GN;
static char **cname; static uint64_t *coff; static int nc;
static uint32_t *boff, *pos; // CSR
static int K, W; static uint64_t KM;

static inline uint64_t h64(uint64_t key, uint64_t mask) {   // invertible mix (as in minimap2)
  key = (~key + (key << 21)) & mask; key = key ^ key >> 24;
  key = ((key + (key << 3)) + (key << 8)) & mask; key = key ^ key >> 14;
  key = ((key + (key << 2)) + (key << 4)) & mask; key = key ^ key >> 28;
  key = (key + (key << 31)) & mask; return key;
}
static int enc(int c) { switch (c) { case 'A': case 'a': return 0; case 'C': case 'c': return 1;
  case 'G': case 'g': return 2; case 'T': case 't': return 3; default: return 4; } }

// call f(p, hash) for each minimizer start p of s[0..n)
#define MINIMIZERS(s, n, ...) do { \
  uint64_t code = 0; int good = 0; uint64_t hq[64]; int64_t last = -1; \
  for (int64_t i = 0; i < (int64_t)(n); i++) { \
    int cc_ = (s)[i]; if (cc_ > 3) { good = 0; code = 0; continue; } \
    code = ((code << 2) | cc_) & KM; good++; \
    if (good >= K) { int64_t st = i - K + 1; hq[st % W] = h64(code, KM); \
      if (good >= K + W - 1) { int64_t ws = st - W + 1; int64_t bp = ws; uint64_t bh = hq[ws % W]; \
        for (int64_t q = ws + 1; q <= st; q++) if (hq[q % W] < bh) { bh = hq[q % W]; bp = q; } \
        if (bp != last) { last = bp; int64_t P_ = bp; uint64_t H_ = bh; __VA_ARGS__ } } } } } while (0)

static void load(const char *fa) {
  FILE *f = fopen(fa, "r"); assert(f);
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  G = malloc(sz); cname = malloc(1000 * sizeof(char *)); coff = malloc(1001 * 8); GN = 0; nc = 0;
  char *line = malloc(1 << 20);
  while (fgets(line, 1 << 20, f)) {
    if (line[0] == '>') { line[strcspn(line, " \t\n")] = 0; cname[nc] = strdup(line + 1); coff[nc++] = GN; continue; }
    for (char *p = line; *p && *p != '\n'; p++) G[GN++] = enc(*p);
  }
  coff[nc] = GN; fclose(f); free(line);
  fprintf(stderr, "genome %lu letters, %d records\n", GN, nc);
}

static void build(void) {
  uint64_t nb = 1ULL << BB; int sh = 2 * K - BB; assert(sh >= 0);
  boff = calloc(nb + 1, 4); assert(boff);
  uint64_t tot = 0;
  for (int c = 0; c < nc; c++) { uint8_t *s = G + coff[c]; uint64_t n = coff[c + 1] - coff[c];
    MINIMIZERS(s, n, { (void)P_; boff[(H_ >> sh) + 1]++; tot++; }); }
  for (uint64_t b = 0; b < nb; b++) boff[b + 1] += boff[b];
  assert(tot < 4294967295ULL);
  pos = malloc(tot * 4); assert(pos);
  uint32_t *fill = malloc(nb * 4); memcpy(fill, boff, nb * 4);
  for (int c = 0; c < nc; c++) { uint8_t *s = G + coff[c]; uint64_t n = coff[c + 1] - coff[c];
    MINIMIZERS(s, n, { pos[fill[H_ >> sh]++] = (uint32_t)(coff[c] + P_); }); }
  free(fill);
  fprintf(stderr, "index k=%d w=%d: %lu entries (%.2f GB)\n", K, W, tot, (tot * 4.0 + nb * 4.0) / 1e9);
}

static int chromOf(uint64_t p) { int lo = 0, hi = nc - 1; while (lo < hi) { int m = (lo + hi + 1) / 2; if (coff[m] <= p) lo = m; else hi = m - 1; } return lo; }

// semi-global banded affine: read r[0..n) vs genome window around diagonal d (genome start of read letter 0)
// returns min penalty (or 1e9) and the genome start of the best alignment
#define INF 1000000
static int band;
static int align(const uint8_t *r, int n, int64_t d, int cap, int64_t *gst) {
  int64_t g0 = d - band, g1 = d + n + band; if (g0 < 0) g0 = 0; if (g1 > (int64_t)GN) g1 = GN;
  int m = (int)(g1 - g0); if (m <= 0) return INF;
  static int *H = 0, *E = 0, *Fv = 0, *S = 0, *H2 = 0, *E2 = 0, *S2 = 0; static int cap_ = 0;
  if (m + 1 > cap_) { cap_ = m + 1; H = realloc(H, cap_ * 4); E = realloc(E, cap_ * 4); Fv = realloc(Fv, cap_ * 4);
    S = realloc(S, cap_ * 4); H2 = realloc(H2, cap_ * 4); E2 = realloc(E2, cap_ * 4); S2 = realloc(S2, cap_ * 4); }
  // row 0: free start anywhere in the window
  for (int j = 0; j <= m; j++) { H[j] = 0; E[j] = INF; S[j] = j; }
  for (int i = 1; i <= n; i++) {
    int64_t dc = d - g0 + i;  // expected column
    int jlo = (int)(dc - band - 1), jhi = (int)(dc + band + 1); if (jlo < 0) jlo = 0; if (jhi > m) jhi = m;
    for (int j = 0; j <= m; j++) { H2[j] = INF; E2[j] = INF; S2[j] = 0; }
    int F = INF, Fs = 0;
    if (jlo == 0) { H2[0] = 6 + 2 * i; S2[0] = 0; }
    for (int j = (jlo < 1 ? 1 : jlo); j <= jhi; j++) {
      // E: gap in genome (read letter consumed): from row i-1 same column
      int e1 = H[j] + 8, e2 = E[j] + 2; int e = e1 < e2 ? e1 : e2; int es = e1 < e2 ? S[j] : S2[j]; (void)es;
      E2[j] = e;
      int f1 = H2[j - 1] + 8, f2 = F + 2; F = f1 < f2 ? f1 : f2; Fs = f1 < f2 ? S2[j - 1] : Fs;
      int c = G[g0 + j - 1]; int mm = (c == r[i - 1] && c < 4) ? 0 : 4;
      int h = H[j - 1] + mm; int hs = S[j - 1];
      if (e < h) { h = e; hs = S[j]; }
      if (F < h) { h = F; hs = Fs; }
      H2[j] = h; S2[j] = hs;
    }
    int *t; t = H; H = H2; H2 = t; t = E; E = E2; E2 = t; t = S; S = S2; S2 = t;
  }
  int best = INF; int bs = 0; for (int j = 0; j <= m; j++) if (H[j] < best) { best = H[j]; bs = S[j]; }
  *gst = g0 + bs; return best;
}

typedef struct { int64_t st; int pen; int strand; } Pl;
static int cmp64(const void *a, const void *b) { int64_t x = *(const int64_t *)a, y = *(const int64_t *)b; return x < y ? -1 : x > y; }
static uint64_t nLook, nHits, nSkip, nDP;

static int mapMate(const uint8_t *r, int n, int maxocc, int cap, Pl *out, int maxout) {
  int k = 0; int sh = 2 * K - BB;
  uint8_t rc[1024]; assert(n < 1024);
  for (int i = 0; i < n; i++) rc[n - 1 - i] = r[i] > 3 ? 4 : 3 - r[i];
  for (int strand = 0; strand < 2; strand++) {
    const uint8_t *s = strand ? rc : r;
    static int64_t dg[200000]; int nd = 0;
    MINIMIZERS(s, n, {
      nLook++; uint64_t b = H_ >> sh; uint32_t lo = boff[b], hi = boff[b + 1]; int cnt = 0; int start = nd;
      if (maxocc && hi - lo > (uint32_t)maxocc + 32) { nSkip++; continue; }
      for (uint32_t t = lo; t < hi; t++) { uint64_t p = pos[t]; if (p < (uint64_t)P_) continue; int ok = 1;
        for (int q = 0; q < K && ok; q++) if (G[p + q] != s[P_ + q]) ok = 0;
        if (ok) { cnt++; if (nd < 200000) dg[nd++] = (int64_t)p - P_; } }
      nHits += cnt; if (maxocc && cnt > maxocc) { nd = start; nSkip++; } });
    // dedup diagonals within band
    qsort(dg, nd, sizeof(int64_t), cmp64);
    int64_t lastd = -1000000;
    for (int i = 0; i < nd; i++) { if (dg[i] - lastd <= band) continue; lastd = dg[i];
      int64_t gs; nDP++; int pen = align(s, n, dg[i], cap, &gs);
      if (pen > cap) continue;
      if (k > 0 && out[k - 1].strand == strand && llabs(out[k - 1].st - gs) <= band) { if (pen < out[k - 1].pen) { out[k - 1].pen = pen; out[k - 1].st = gs; } continue; }
      if (k < maxout) { out[k].st = gs; out[k].pen = pen; out[k].strand = strand; k++; } }
  }
  return k;
}

static int readRec(FILE *f, char *name, uint8_t *seq, int *n) {
  char l1[4096], l2[4096], l3[4096], l4[4096];
  if (!fgets(l1, 4096, f) || !fgets(l2, 4096, f) || !fgets(l3, 4096, f) || !fgets(l4, 4096, f)) return 0;
  l1[strcspn(l1, " \t\n")] = 0; strcpy(name, l1 + 1);
  int m = (int)strcspn(l2, "\n"); for (int i = 0; i < m; i++) seq[i] = enc(l2[i]); *n = m; return 1;
}

// sim name: s0:chr11:12961789-12961939+:12961931-12962081-
static int truthOf(const char *name, char *chr, int64_t *a, int64_t *b) {
  char tmp[512]; strcpy(tmp, name); char *p = strchr(tmp, ':'); if (!p) return 0; p++;
  char *q = strchr(p, ':'); if (!q) return 0; *q = 0; strcpy(chr, p);
  long x, y; if (sscanf(q + 1, "%ld-%*ld%*c:%ld", &x, &y) != 2) return 0; *a = x; *b = y; return 1;
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "ss GENOME.fa K W MAXOCC CAP r1 r2 ...\n"); return 1; }
  K = atoi(argv[2]); W = atoi(argv[3]); int occs[16], nocc = 0; for (char *t = strtok(argv[4], ","); t; t = strtok(0, ",")) occs[nocc++] = atoi(t); int cap = atoi(argv[5]);
  KM = (K == 32) ? ~0ULL : ((1ULL << (2 * K)) - 1); assert(W <= 64);
  band = (cap - 6) / 2 + 1; if (band < 1) band = 1;
  clock_t t0 = clock(); load(argv[1]); build();
  fprintf(stderr, "load+build %.1f s cpu\n", (double)(clock() - t0) / CLOCKS_PER_SEC);
  for (int a = 6; a + 1 < argc; a += 2) for (int oi = 0; oi < nocc; oi++) { int maxocc = occs[oi];
    FILE *f1 = fopen(argv[a], "r"), *f2 = fopen(argv[a + 1], "r"); assert(f1 && f2);
    char n1[512], n2[512]; uint8_t s1[1024], s2[1024]; int l1, l2;
    long pairs = 0, found = 0, uniq = 0, truth = 0, sims = 0, one = 0; long hist[8] = {0}; long mx[3] = {0}, mxT[3] = {0};
    nLook = nHits = nSkip = nDP = 0; clock_t t1 = clock();
    static Pl p1[4096], p2[4096];
    while (readRec(f1, n1, s1, &l1) && readRec(f2, n2, s2, &l2)) {
      pairs++;
      int k1 = mapMate(s1, l1, maxocc, cap, p1, 4096), k2 = mapMate(s2, l2, maxocc, cap, p2, 4096);
      if (k1 || k2) one++;
      int best = INF, second = INF; int64_t b1 = 0, b2 = 0; int bm = 0;
      for (int i = 0; i < k1; i++) for (int j = 0; j < k2; j++) {
        if (p1[i].strand == p2[j].strand) continue;
        int c1 = chromOf(p1[i].st), c2 = chromOf(p2[j].st); if (c1 != c2) continue;
        int64_t fw = p1[i].strand == 0 ? p1[i].st : p2[j].st, rv = p1[i].strand == 0 ? p2[j].st : p1[i].st;
        int64_t frag = rv + (p1[i].strand == 0 ? l2 : l1) - fw;
        if (frag < 100 || frag > 1000) continue;
        int s = p1[i].pen + p2[j].pen;
        if (s < best) { second = best; best = s; b1 = p1[i].st; b2 = p2[j].st; bm = p1[i].pen > p2[j].pen ? p1[i].pen : p2[j].pen; } else if (s < second) second = s;
      }
      if (best < INF) { found++; if (second > best) uniq++; int h = best / 8; if (h > 7) h = 7; hist[h]++; int mb = bm <= 16 ? 0 : bm <= 24 ? 1 : 2; mx[mb]++;
        char tc[64]; int64_t ta, tb;
        if (truthOf(n1, tc, &ta, &tb)) { sims++; int c = chromOf(b1);
          int64_t q1 = b1 - (int64_t)coff[c] + 1, q2 = b2 - (int64_t)coff[c] + 1;
          if (!strcmp(cname[c], tc) && llabs(q1 - ta) <= 20 && llabs(q2 - tb) <= 20) { truth++; mxT[mb]++; } } }
    }
    double cs = (double)(clock() - t1) / CLOCKS_PER_SEC;
    printf("%s k=%d w=%d maxocc=%d cap=%d: pairs %ld, a mate placed %ld, proper pair %ld, unique %ld, at truth %ld (of %ld checked); "
           "lookups %lu, exact hits %lu (%.1f/lookup), skipped %lu, DPs %lu; %.1f s cpu (%.2f ms/pair); pair pen hist /8:",
           argv[a], K, W, maxocc, cap, pairs, one, found, uniq, truth, sims, nLook, nHits, nLook ? (double)nHits / nLook : 0.0,
           nSkip, nDP, cs, pairs ? 1000.0 * cs / pairs : 0.0);
    for (int h = 0; h < 8; h++) printf(" %ld", hist[h]); printf("; worse mate <=16/<=24/<=32: %ld %ld %ld (at truth %ld %ld %ld)\n", mx[0], mx[1], mx[2], mxT[0], mxT[1], mxT[2]); fflush(stdout);
    fclose(f1); fclose(f2);
  }
  return 0;
}
