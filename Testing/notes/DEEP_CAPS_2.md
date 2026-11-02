# deepCaps, part 2: why the shim pays more than the bench (box O2, 2026-11-02)

Box: 4 vCPU, 15 GB, release `bench-release`; tree festive-fermi 2b496d6. Bench index made from shim.idx (same
bytes: `.sl`/`.pgw` hardlinks, `.offs`/`.runs`/`.meta`/`.pgx`/`.pgc` written from `Spec.loadIndex`'s result;
converter in the session scratchpad, not committed). Bench: `WG_NOCHECK=1 WG_MODES=RTX WG_XH=0`, deepCaps on =
`WG_PASS2=1 WG_P2BUDGET=3000 WG_T2=250:28,150:20` (the shim's `tierCfg` with `deepCaps := true`, field by field).

## Cause: the shim maps untrimmed reads
The bench reads every mate through the proved quality trimmer (`ReadTrim.trimReadQ`, `readMates`). The shim does
not trim (`Spec/Shim.lean` / `Main.lean`: "Stand-ins for now: no trimming"). HiSeq 2×250 tails are low quality:
untrimmed mates miss cap 16 (`XB:i:-17`), stay `boundsOnly`, and all of them go to pass 2, where the genome-wide
stage B runs a banded DP on nearly every anchor diagonal.

| 2000 HiSeq pairs, callgrind Ir inside `tierPair` | off | on |
|---|---|---|
| shim (untrimmed) | 1.13 G | 3.74 G |
| bench (trimmed) | 4.29 G | 5.10 G |
Stage-B banded DPs in pass 2: shim 306k, bench 92k. Pass 1: bench keeps 1,655 of 2,000 as unique, shim 1,436; of
the difference, 197 pairs are unique in the bench and `boundsOnly` in the shim.

## Shim on the bench's trimmed mates (`WG_TRIMOUT`, quality 'I'), 4 cores, CPU s, 2 warm runs
| set | reads | off | on | pass-2 cost | unique pairs off → on |
|---|---|---|---|---|---|
| HiSeq 200k | untrimmed | 23.6 / 25.5 | 58.2 / 59.2 | +135% | 140,974 → 150,342 |
| HiSeq 200k | trimmed | 27.9 (cold run 42.8 dropped) | 40.4 / 38.4 | ~+40% | 163,634 → 165,485 |
| NovaSeq 200k | untrimmed | 34.0 / 35.0 | 39.9 / 39.2 | +14% | 162,941 → 164,535 |
| NovaSeq 200k | trimmed | 27.2 / 30.6 | 32.9 / 32.0 | +12% | 163,865 → 164,698 |
(unique pairs = `XT:Z:eachMateUnique` lines / 2; the bench keeps 164,485 HiSeq / 165,205 NovaSeq pairs at deepCaps off.)

## Proposed change (Rowan's file; text only, not applied)
`Spec/Shim.lean` (and `Main.lean`, which mirrors it), `chunkPairs`: trim each mate with the proved trimmer; a mate
trimmed away is `none` (the spec already allows `none` = trimmed away):
```lean
def Spec.chunkPairs (chunk : Array (Spec.FastqRecord × Spec.FastqRecord)) :
    List (Option ByteArray × Option ByteArray) :=
  let trim (r : Spec.FastqRecord) : Option ByteArray :=
    (ReadTrim.trimRead r.letters r.quality.toUTF8).map fun (b, e) => r.letters.extract b e
  chunk.toList.map fun (record1, record2) => (trim record1, trim record2)
```
(needs `import ReadTrim` in the shim; SAM output then reports the trimmed window, so SAM changes: a decision.)
Effect: +22.7k unique HiSeq pairs per 200k at deepCaps off; deepCaps' HiSeq cost +135% → ~+40%.

## Knobs in `tierCfg` alone (untrimmed reads; not a fix)
2000 HiSeq pairs, Ir in `tierPair`: today's deepCaps 3.74 G; gate2 budget 1000: 3.28 G; 250 bp cap 24: 3.65 G;
both: 2.86 G — each loses 1.1k–4.4k of the 18.7k extra unique mate lines per 200k. `alignPairs` sees no qualities,
so the trimming cannot be done on our side.

## Side findings
- After O1's thread fix the bench is no longer a proxy for the shim: it uses ~2× the shim's CPU (no per-task index
  copy, contended counts) and 3.8× its Ir in pass 1 (per-chromosome routing; the shim routes on one sequence).
- Remaining gap with trimmed reads (HiSeq +40% vs bench +16%): not traced yet.

## Short-seed prototype (unproved, measurement only; `Testing/scripts/shortseed/ss.c`)
`gcc -O2 -march=native -o ss ss.c`; `ss genome.fa K W MAXOCC[,..] CAP r1 r2 ...`. Forward-strand (K, W) minimizer
index of hg38 in memory (CSR by the hash's top 28 bits); per mate and strand: read minimizers → exact hits (verified
on the genome; a seed with more than MAXOCC exact hits is skipped, 0 = keep all) → diagonals → banded affine DP
(mismatch 4, open 6, extend 2; read end to end) → placements ≤ CAP → FR pairs, fragment 100..1000. A clean stretch of
K + W − 1 letters always yields a hit (K = 21, W = 4: 24 letters).
hg38, K = 21, W = 4: 1.17 G entries, 5.8 GB, 512 s single-thread build.

Input: the pairs the shim leaves `boundsOnly` today (HiSeq/NovaSeq trimmed as above; mason/low as released):
HiSeq 28,893, NovaSeq 27,454, mason 18,887, low 6,212 of 200k. First 1000 of each, cap 32, ms = CPU per pair
(single thread). "worse mate" = the larger mate penalty of the best pair (≤16 = the proved mapper gave up on it for
another reason: gate / repeats / ties; 17–32 = needs the deeper cap).

| set | MAXOCC | proper pair | unique | at truth | worse mate ≤16 / ≤24 / ≤32 (at truth) | ms/pair |
|---|---|---|---|---|---|---|
| mason | 20 | 875 | 776 | 789 | 193 / 615 / 67 (131 / 599 / 59) | 17.5 |
| mason | 100 | 919 | 809 | 822 | 221 / 631 / 67 (152 / 611 / 59) | 30.6 |
| mason | 500 | 954 | 824 | 850 | 250 / 639 / 65 (171 / 618 / 61) | 79.5 |
| low | 20 | 696 | 520 | 519 | 487 / 175 / 34 (352 / 163 / 4) | 29.4 |
| low | 100 | 766 | 564 | 573 | 555 / 182 / 29 (405 / 164 / 4) | 46.2 |
| low | 500 | 858 | 610 | 648 | 656 / 180 / 22 (480 / 164 / 4) | 111.8 |
| HiSeq | 20 | 378 | 320 | – | 181 / 124 / 73 | 34.3 |
| HiSeq | 100 | 417 | 334 | – | 213 / 124 / 80 | 80.2 |
| HiSeq | 500 | 459 | 346 | – | 247 / 135 / 77 | 269.2 |
| NovaSeq | 20 | 485 | 412 | – | 226 / 159 / 100 | 25.1 |
| NovaSeq | 100 | 530 | 430 | – | 261 / 166 / 103 | 38.9 |
| NovaSeq | 500 | 563 | 433 | – | 298 / 166 / 99 | 108.5 |
No occurrence limit (100 low pairs): 99 proper, 69 at truth, 4.1 s/pair (1,900 exact hits per lookup).

Scaled to 200k pairs (MAXOCC 20): mason +14.9k pairs at truth (+7.5%), low +3.2k (+1.6%); HiSeq +9.2k unique pairs
(+4.6%; ~half need the deeper cap), NovaSeq +11.3k (+5.7%). Cost as measured is far too high (HiSeq 28.9k × 34 ms ≈
990 s CPU vs ~28 s for the whole shim run): the prototype verifies every entry of a bucket before deciding to skip it
(1,600–2,150 entries per lookup in these repeat-rich pairs); the DPs are few (60–120 per pair at MAXOCC 20).

K = 18, W = 4 (21-letter clean stretch), same 1000-pair inputs: mason MAXOCC 20 / 100: 864 / 920 proper, 782 / 821 at
truth, 32.8 / 51.4 ms; low 682 / 763, 508 / 568 at truth, 53.3 / 79.6 ms; HiSeq 382 / 417 proper (325 / 337 unique),
75.2 / 139.0 ms; NovaSeq 484 / 534 (414 / 435 unique), 53.7 / 75.2 ms. Same gains as K = 21 (±1–2%) at 1.7–2.2× the
cost (exact hits per lookup 1,731–4,630): the 24-letter guarantee of K = 21 already covers these pairs.
