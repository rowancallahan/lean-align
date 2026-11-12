# Deeper error caps (EXPERIMENTS_NEXT.md §3), box O3, 2026-11-02

Branch `speed/n31-deep-caps` (from `claude/festive-fermi-mf9mo6` 5c309c3). hg38 bench index built here
(`whole_genome build` + WG_CHECK=1: check3P true, 728 s). 4 cores, 15 GB RAM.

## 1. Which seeds guarantee a clean seed

The bound in use is the event bound `seedBoundE` (MapperEvents, behind `sbound` / `fastT`): with the default
scoring (0, −4, −6, −2) a walk within penalty P spoils at most ⌊P/4⌋ disjoint seeds (each mismatch, each gap run,
plus one per seed boundary a gapY run crosses; seeds ≥ 2 letters). `exists_clean_seed_amongE` is generic in the
seed count, so m = ⌊P/4⌋ + 1 disjoint seeds of ⌊n/m⌋ letters always contain a clean one (gap bounds
d = (P−6)/2, d2 = (P−12)/2 for the window shapes).

| errors | P | seeds m | seed length at 150 bp | at 250 bp |
|---|---|---|---|---|
| 4 | 16 | 5 | 30 | 50 |
| 5 | 20–23 | 6 | 25 (today's index: max at 150 bp) | 41 |
| 6 | 24 | 7 | 21 (new index) | 35 |
| 7 | 28 | 8 | 18 (new index) | 31 |
| 8 | 32 | 9 | 16 | 27 |
| 9 | 36–39 | 10 | 15 | 25 (today's index: max at 250 bp) |

- 250 bp mates need no new index up to P = 39; 150 bp mates up to P = 23 (pass 2 of the router, already proved).
- Overlapping 25-mers from the same index cannot give a guarantee at 6+ errors on 150 bp: the longest error-free
  stretch is only ≥ (150 − 6)/7 ≈ 20.6 letters. Spaced seeds would need their own index and a new pigeonhole proof
  (and a gap inside the span spoils them); contiguous shorter seeds reuse the proved machinery
  (`exists_clean_seed_amongE`, SeedMapper2's generic `l0`), so they are the recommended shape.

Seed cost on hg38 (`Testing/scripts/deepcaps/dc.c kmer`: exact occurrence counts, both strands, of each disjoint
L-letter seed; one genome pass per L):

| L | hits/seed mean | median | p99 | hits per mate, all seeds: random 20k mason mates | the 31,748 mates still unmapped after pass 2 at 20 |
|---|---|---|---|---|---|
| 25 | 690 | 1 | 13.5k | 4,142 | 7,930 |
| 21 | 1,498 | 1 | 36k | 10,485 | 17,122 (2.2×) |
| 18 | 3,098 | 1 | 80k | 24,786 | 33,441 (4.2×) |
| 16 | 4,838 | 5 | 123k | 43,538 | – |
| 14 | 8,037 | 57 | 168k | 80,371 | – |

The cost is in a few repeat mates: on the still-failing mates, a 10k-hit budget per pair keeps 61% of pairs and
1.0% (L=21) / 0.5% (L=18) of all hits.

## 2. What is there to gain (truth penalties) and what the proved pass 2 already gets

`dc truth`: glocal affine DP (0/−4/−6/−2) of each trimmed mate (WG_TRIMOUT) against its true locus ±40,
traceback → errReps-style coordinates. hg38 mason 2×150 200k (penalties are multiples of 4: mason errors are
mostly mismatches):

| worst mate's truth penalty | all pairs | left unmapped by the default (RTX) |
|---|---|---|
| ≤ 16 | 186,289 | 10,414 (ties, not proper, ...) |
| 17–20 | 9,778 | 9,778 |
| 21–23 | 1 | 1 |
| 24 | 2,930 | 2,930 |
| 25–28 | 778 | 778 |
| 29–40 | 224 | 224 |

In practice a clean disjoint 25-mer exists in both mates for 98.8% of the P=24 pairs and 95.6% of the 25–28 pairs
— the deeper index is needed for the *proof* (no other hit within the cap), not to find the truth.

Proved pass 2 (`RouteCfg.pass2`, `routeG_ok`; bench WG_PASS2=1), one run each, CPU of the mapping:

| mason 200k | kept = at truth | gained | CPU s |
|---|---|---|---|
| default | 175,871 (87.94%) | – | 59.1 |
| pass 2 at 20 (150:20), no gate | 184,122 (92.06%) | +8,251 | 109.0 (+85%) |
| + gate both mates' costP ≤ 1000 | | +6,731 | 59.7 |
| + gate ≤ 3000 | | +7,075 | 63.0 |
| + gate ≤ 10000 | | +7,456 | 72.8 |
| 150:23 | same pairs as 150:20 (no penalty 21–23) | | 110.9 |

No pair lost, every gained pair at truth (4 kept-not-at-truth pairs in every run, the same 4).

Real reads, one run each: HiSeq 2×250 (T2=250:28,150:20, gate 3000) kept 166,490 → 168,345 (+1,855, +1.1%);
250:36 gives 168,274 (deeper cap: more ties). NovaSeq 2×151 (150:20, gate 3000) 167,819 → 168,656 (+837).

## 3. Timing vs minibwa (median of 3, interleaved, 4 threads on cores 0–3, mapping only)

Ours: bench RTX `RESULT` (index load excluded). minibwa c07de5c (default `make` and `-march=native`), prebuilt
release index: Real time − "index loaded" time; CPU − load time × its CPU ratio. Multiple = minibwa ÷ ours
(> 1: we are faster). p2g3k = WG_PASS2=1 WG_P2BUDGET=3000, T2 = 150:20 (mason, NovaSeq) / 250:28,150:20 (HiSeq).

| set | config | kept | wall s | CPU s | × mb default wall / CPU | × mb native wall / CPU |
|---|---|---|---|---|---|---|
| mason 2×150 | default | 175,875 | 15.81 | 62.3 | 0.77 / 0.75 | 0.82 / 0.78 |
| | p2g3k | 182,950 | 15.94 | 62.7 | 0.77 / 0.74 | 0.81 / 0.77 |
| | minibwa | | 12.23 / 12.95 | 46.4 / 48.4 | | |
| HiSeq 2×250 | default | 166,490 | 8.03 | 31.5 | 2.90 / 2.83 | 2.83 / 2.77 |
| | p2g3k | 168,345 | 10.37 | 40.6 | 2.24 / 2.19 | 2.19 / 2.14 |
| | minibwa | | 23.27 / 22.73 | 89.2 / 87.1 | | |
| NovaSeq 2×151 | default | 167,819 | 9.27 | 36.2 | 1.28 / 1.24 | 1.27 / 1.23 |
| | p2g3k | 168,656 | 10.14 | 39.9 | 1.17 / 1.12 | 1.16 / 1.11 |
| | minibwa | | 11.85 / 11.80 | 44.9 / 44.3 | | |

Pairs at truth on mason: default 175,871 (87.94%), p2g3k 182,946 (91.47%; the gated runs are a subset of the
ungated run's pairs, all at truth). minibwa default: both mates mapped 200,000, both at truth 196,349 (98.17%);
both MAPQ > 0 194,956, of which at truth 194,767 (97.38%).

HiSeq variants (one run each, base 31.5 s CPU median): 250:28 gate 1000 +1,746 pairs / 37.7 s; 250:24 gate 3000
+1,778 / 39.0 s; 150:20 only (250 bp mates also at 20) +1,656 / 41.1 s. On real 2×250 reads the pass-2 pairs are
mostly dead reads (no hit anywhere), so pass 2 costs +20–30% CPU for +1.0–1.1% pairs; on mason it is ~free.

## 4. Iterative deepening as built

The router already is iterative deepening: pass 1 at today's caps, pass 2 at the deeper caps only for pairs whose
reason is noHit / noPartner / tooShort (`goOn`), and only when `gate2` lets them through (a held-back pair keeps its
pass-1 settlement; exact for any gate, `routeG_ok`). The gain is concentrated in cheap pairs: the gate keeps
86% of the gain at ~1% of the no-gate cost.

**Proved version, default off** (this branch): `Proofs/Aligner.lean` `deepCaps : Bool := false`; when true,
`tierCfg` sets `pass2 := true`, `cap2 := 28 (≥ 250) / 20 (150–249)`, `gate2 := both mates' costP at the pass-2 cap
≤ 3000`. Nothing else changes; `tierPair_sound` holds for every `TierCfg`, so `alignPairs_correct` is untouched.
Default output byte-identical (pass2 false: `routeG` never evaluates cap2/gate2). Checked: shim on chr21 +
the 2,563 chr21 mason pairs, SAM of this branch = SAM of 5c309c3 (`cmp`); built with `deepCaps := true` the same
run gives `XT:Z:eachMateUnique` 2,198 → 2,313 pairs, `boundsOnly` 171 → 96. CI_check passes.

**Recommendation:** turn `deepCaps` on (Rowan's call: it changes output). On mason +3.5 points of pairs at
truth for +0.6% CPU (median); on real reads +1.1% (HiSeq) / +0.5% (NovaSeq) pairs for +29% / +10% CPU — a gate of
1000 roughly halves the HiSeq cost (+1,746 pairs at +20%). Do the 24/28 index (section 5) only after that.

## 5. What the proved 24/28 caps at 150 bp need

1. **A second index for L-letter seeds** (L = 21 for P = 24, 18 for P = 28). Options: (a) every position:
   3.1 G entries ≈ 12 GB — too large next to today's index on a 16 GB box; (b) a minimizer index with k + w − 1 = L
   (e.g. k = 18, w = 4 for L = 21; k = 15, w = 4 for L = 18): density ~2/(w+1) ≈ 1.2 G entries ≈ 5–6 GB, built and
   checked like today's (`Mz.check`-style completeness: every true occurrence reported; collisions harmless). The
   existing 22-mer minimizer index cannot serve shorter seeds (a 21-letter seed contains no 22-mer).
2. **Seed length as a parameter of the fast mapper.** FastGen / kpKer hard-code 25 (`R.size / 25`, `fastT`,
   25-letter word code `wN`). The pigeonhole (`exists_clean_seed_amongE`) and the slow mapper (SeedMapper2, `l0`)
   are already generic; the fast kernels' seed loop, `sbound`-based stops and stage-B support count
   (`#seeds − sbound`) need the seed length as a parameter.
3. **Router:** `fastT` (25-letter) gates `cap2Of` and the `tooShort` reason; a deep kernel needs its own fast-path
   predicate in `PassKer`/`KerOk` (`fast : Nat → ByteArray → Bool`, with `KerOk` asking `MateOk` only where it holds)
   so pass 2 can use a cap the 25-mer seeds cannot reach. `routeG_ok` / `tierPair_sound` keep their statements
   with `fastT` replaced by the kernel's predicate in `Settled`'s tooShort case (more general, not weaker).
4. **Bound proof for the deeper cap:** nothing new — `seedBoundE` at P = 24 / 28 is 6 / 7 (decide), and
   `exists_clean_seed_amongE` with k + 1 = 7 / 8 seeds of ⌊n/7⌋ / ⌊n/8⌋ ≥ 2 letters.
5. Support is 1 (m − sbound = 1) for 7×21 at P = 24 and 8×18 at P = 28: every hit is a candidate; only the gate keeps
   it cheap. 9×16 at P = 28 gives support 2 (diagonal pairs) at 1.8× the lookups of 18-mers.

Expected value on mason: ≤ +2,930 pairs (1.5%) at P = 24 and ≤ +778 more at P = 28 (upper bounds: ties and partner
logic will take some); proxy cost with a 10k-hit gate ~1% of the hits of an ungated pass. Real reads (HiSeq/NovaSeq)
gain far less from pass 2 than the sims (+1.1% / +0.5%), so the 24/28 step is mainly a sim-accuracy item.

## Tools
- `Testing/scripts/deepcaps/dc.c` (`gcc -O2 -o dc dc.c`): `dc truth`, `dc kmer` (see the header).
- `Testing/scripts/deepcaps/analyze.py`: truth bins, kept / at truth per RTX dump, clean-seed table.
  Note: the bench reads the multi-record FASTA as ONE sequence; later header lines stay in it as letters
  (analyze.py maps hit offsets back to records accordingly).
