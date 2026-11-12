// kcount K KMERS GENOME CAP OUT
// For every k-mer in KMERS (one per line, ACGT), count its occurrences in GENOME (FASTA), on either strand
// (canonical k-mer), and keep up to CAP positions: global offset (letters of earlier chromosomes summed)
// and the strand on which the listed k-mer itself occurs (0: as listed, 1: reverse complement).
// OUT lines: kmer count pos:strand pos:strand ...   (positions only when count <= CAP)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>

static int K;
static uint64_t MASK;
static int code(int c) {
  switch (c) { case 'A': case 'a': return 0; case 'C': case 'c': return 1; case 'G': case 'g': return 2;
    case 'T': case 't': return 3; default: return -1; }
}
static uint64_t rc(uint64_t x) {
  uint64_t r = 0;
  for (int i = 0; i < K; i++) { r = (r << 2) | (3 - (x & 3)); x >>= 2; }
  return r;
}
typedef struct { uint64_t key; uint32_t cnt; uint32_t n, cap; uint64_t *pos; } E;
static E *tab; static uint64_t tsz;
static uint64_t h(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static E *find(uint64_t key, int ins) {
  uint64_t i = h(key) & (tsz - 1);
  while (1) {
    if (tab[i].cap == 0xffffffffu) { if (!ins) return NULL; tab[i].key = key; tab[i].cap = 0; return &tab[i]; }
    if (tab[i].key == key) return &tab[i];
    i = (i + 1) & (tsz - 1);
  }
}
int main(int argc, char **argv) {
  assert(argc == 6);
  K = atoi(argv[1]); assert(K >= 8 && K <= 31);
  MASK = (K == 32) ? ~0ULL : ((1ULL << (2 * K)) - 1);
  uint32_t CAP = (uint32_t)atoi(argv[4]);
  FILE *fk = fopen(argv[2], "r"); assert(fk);
  char line[256]; uint64_t nk = 0;
  while (fgets(line, sizeof line, fk)) nk++;
  rewind(fk);
  tsz = 1; while (tsz < 3 * nk + 16) tsz <<= 1;
  tab = calloc(tsz, sizeof(E)); assert(tab);
  for (uint64_t i = 0; i < tsz; i++) tab[i].cap = 0xffffffffu;
  char **kms = malloc(nk * sizeof(char *)); uint64_t *canon = malloc(nk * 8); uint64_t m = 0;
  while (fgets(line, sizeof line, fk)) {
    int L = (int)strcspn(line, "\r\n"); line[L] = 0; assert(L == K);
    uint64_t x = 0;
    for (int i = 0; i < K; i++) { int c = code(line[i]); assert(c >= 0); x = (x << 2) | (uint64_t)c; }
    uint64_t y = rc(x), cn = x < y ? x : y;
    find(cn, 1); kms[m] = strdup(line); canon[m] = x; m++;
  }
  fclose(fk);
  FILE *fg = fopen(argv[3], "r"); assert(fg);
  static char buf[1 << 20];
  uint64_t gpos = 0, f = 0, r = 0; int valid = 0, inhdr = 0, bol = 1;
  size_t got;
  while ((got = fread(buf, 1, sizeof buf, fg)) > 0) {
    for (size_t i = 0; i < got; i++) {
      char ch = buf[i];
      if (bol && ch == '>') { inhdr = 1; valid = 0; bol = 0; continue; }
      if (ch == '\n') { bol = 1; inhdr = 0; continue; }
      bol = 0;
      if (inhdr) continue;
      int c = code(ch);
      gpos++;
      if (c < 0) { valid = 0; continue; }
      f = ((f << 2) | (uint64_t)c) & MASK;
      r = (r >> 2) | ((uint64_t)(3 - c) << (2 * (K - 1)));
      if (valid < K) valid++;
      if (valid < K) continue;
      uint64_t cn = f < r ? f : r;
      E *e = find(cn, 0);
      if (!e) continue;
      e->cnt++;
      if (e->cnt <= CAP) {
        if (e->n == e->cap) { e->cap = e->cap ? 2 * e->cap : 4; e->pos = realloc(e->pos, e->cap * 8); assert(e->pos); }
        // start of the k-mer (0-based global offset); strand bit: 1 when the genome holds the reverse complement of
        // the canonical form's forward orientation f (resolved per listed k-mer below)
        e->pos[e->n++] = ((gpos - K) << 1) | (f == cn ? 0 : 1);
      }
    }
  }
  fclose(fg);
  FILE *fo = fopen(argv[5], "w"); assert(fo);
  for (uint64_t i = 0; i < m; i++) {
    uint64_t x = canon[i], y = rc(x), cn = x < y ? x : y;
    E *e = find(cn, 0); assert(e);
    // listed k-mer equals cn (flip 0) or rc(cn) (flip 1); genome strand bit s means genome holds cn (0) or rc(cn) (1)
    int flip = (x == cn) ? 0 : 1;
    fprintf(fo, "%s %u", kms[i], e->cnt);
    if (e->cnt <= CAP)
      for (uint32_t j = 0; j < e->n; j++) fprintf(fo, " %llu:%d", (unsigned long long)(e->pos[j] >> 1), (int)((e->pos[j] & 1) ^ flip));
    fputc('\n', fo);
  }
  fclose(fo);
  return 0;
}
