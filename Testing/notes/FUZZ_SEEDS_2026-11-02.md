# Fuzz test on hg38: 3 seeds x 3 modes, both tools, plus a spec-hole audit (2026-11-02)

Head: `origin/claude/festive-fermi-mf9mo6` @ c8d3df5 (includes f3f7be1's `Testing/fuzz/`). The 4-command test of `Testing/fuzz/README.md` on hg38:
`sim_pairs.py hg38.1l.fa fz 10000 {mason,low,high} {1,2,3}` (90 000 pairs, 180 000 mates), `lean-align map shim.idx ... 100 1000`,
`minibwa map -t 4 mb ...` (c07de5c; the three seeds of a mode in one run so its insert-size estimate is per mode), `compare_sam.py ours.sam mb.sam`.
Audit: `Testing/fuzz/audit_vs_minibwa.py ours.sam mb.sam hg38.1l.fa` (new; recomputes scores from the reference with the spec's scoring).

## Result in one line

**No finding that suggests a proof or spec hole.** Rules A-D (below) are zero on all nine sets; no pair is `unique` with minibwa at MAPQ 60 elsewhere and the truth
agreeing with minibwa (rule E: 0). The checks are not vacuous: mutating a copy of one SAM (XB lowered by 100, AS raised by 4, every pair relabelled unique) makes rules B and C,
A, and D fire (9 601 / 10 000, 19 606, 450 hits).

## `compare_sam.py` summary lines (every seed, every mode)

| mode | seed | mates | same position | same position+CIGAR | within 10 bp of truth: ours | minibwa |
|---|---|---|---|---|---|---|
| mason | 1 | 20,000 | 17,676 | 16,563 | 18,744 | 19,605 |
| mason | 2 | 20,000 | 17,691 | 16,671 | 18,702 | 19,566 |
| mason | 3 | 20,000 | 17,556 | 16,476 | 18,636 | 19,564 |
| low | 1 | 20,000 | 18,905 | 18,497 | 19,312 | 19,654 |
| low | 2 | 20,000 | 18,898 | 18,461 | 19,314 | 19,657 |
| low | 3 | 20,000 | 18,853 | 18,408 | 19,249 | 19,645 |
| high | 1 | 20,000 | 15,330 | 14,133 | 16,401 | 19,607 |
| high | 2 | 20,000 | 15,515 | 14,323 | 16,638 | 19,594 |
| high | 3 | 20,000 | 15,516 | 14,362 | 16,575 | 19,622 |

(`compare_sam.py` prints the first 10 differing mates per run; the full categorisation of every differing mate is in the next section.)

## Audit rules, zero tolerated (HARD) on all nine sets

| rule | meaning | hits in 90 000 pairs |
|---|---|---|
| A | `AS` of a mapped record != the score recomputed from CIGAR + SEQ + the reference (match 0, mismatch -4, gap of k letters -(6+2k)) | 0 (every mapped mate) |
| B | `XB` < `AS1 + AS2` on a mapped pair (bound below the pair it reports) | 0 |
| C | `XB` < the score, under our scoring, of a proper pair built from minibwa's placement (the bound would be false) | 0, on 89 992 pairs where minibwa gives a scorable proper pair |
| D | `XU:Z:unique` but minibwa's proper pair is at another placement scoring >= ours (or the same placement scoring higher) | 0 |
| E | `unique`, minibwa MAPQ 60 on both mates elsewhere, and the true origin agrees with minibwa | 0 |

How minibwa's pair is scored: its CIGAR is turned into an end-to-end alignment of exactly our (trimmed) window of the read, soft-clipped letters inside the window
continue the diagonal; properness is the spec's `IsProper` (same chromosome, opposite strands, forward start <= reverse stop, fragment 100..1000, slack 0).
Self-test of that reconstruction: where both tools start both mates at the same position the rebuilt minibwa score equals our `AS1+AS2` on 8 229-9 241 pairs per set
(mason/low) and 6 938-7 047 (high); the remainder (7-14, and 198-217 in `high`) have different CIGARs at the same start.

Our unique pairs against the true origin (both mates within 10 bp, same strand): mason 25 882 unique pairs, 0 off the origin; low 28 227, 3 off (one per seed; minibwa is at the
origin in each, the printed start of one mate is moved by trimming, e.g. ours `chr3:145044723 139M` vs minibwa `chr3:145044712 150M`); high 17 749, 15 off (6 + 6 + 3): minibwa is at the
origin for 9 of them (again mostly a trimmed start, e.g. ours `chr5:92595901 135M` vs minibwa `92595886 150M`, truth 92595885) and neither tool is for the other 6.
In none of these does minibwa's pair score >= ours at a different placement (that would be rule D, which is 0).

## Every differing mate, by category (all nine sets; mates, of 180 000)

| category | mason | low | high | all |
|---|---|---|---|---|
| ours unmapped, minibwa maps | 1216 | 118 | 6964 | 8298 |
| ours inside minibwa (trimmed/clipped more) | 2911 | 1156 | 2721 | 6788 |
| different chromosome or strand: minibwa at truth | 1061 | 856 | 1190 | 3107 |
| different chromosome or strand: ours is a placeholder (no M) | 596 | 86 | 1382 | 2064 |
| different chromosome or strand: neither at truth | 407 | 345 | 279 | 1031 |
| minibwa inside ours (it clips more) | 264 | 43 | 429 | 736 |
| same chromosome, disjoint: neither at truth | 215 | 268 | 177 | 660 |
| same chromosome, disjoint: minibwa at truth | 189 | 260 | 187 | 636 |
| different chromosome or strand: ours at truth | 142 | 150 | 131 | 423 |
| same chromosome, disjoint: ours at truth | 56 | 56 | 31 | 143 |
| shifted overlap | 6 | 6 | 90 | 102 |
| same chromosome, disjoint: ours is a placeholder (no M) | 14 | 0 | 58 | 72 |

Reading the large rows (they are our known weak spots, not label errors):
- "ours unmapped, minibwa maps": `high` 6 964 of 60 000 mates (11.6 %) vs mason 1 216 (2.0 %), low 118 (0.2 %). Heavy-error reads exceed our caps (-12/-16) and the bound cannot certify them.
- "different chromosome or strand: minibwa at truth" 3 107 and "ours at truth" only 423: where we place a mate elsewhere, it is almost always a pair we do not call unique (fallback pairs, MAPQ 0),
  never a unique claim (rule E and D are zero; the unique pairs are at the origin, previous section).
- "ours is a placeholder (no M)": 2 064 + 72 mates, the degenerate last-resort pair (below).
- "ours inside minibwa" 6 788: trimming/clipping of ends (we align the trimmed window, minibwa the soft-clipped read).
- "minibwa unmapped, ours maps": 0.

## Degenerate CIGARs (`^[0-9]+I$`, the placeholder pair at chr1:1 / chr1:101)

mason 194 / 208 / 208 mates (seeds 1-3; 0.97-1.04 % of mates), low 34 / 26 / 26 (0.13-0.17 %), high 510 / 514 / 416 (2.1-2.6 %); every one of them is also a CIGAR without any M.
This is the known `reportFloor`/last-resort item from SESSION_SUMMARY; the numbers here are the baseline before the floor is added.

## Not covered

Repeat-masked check from the earlier note (needs the soft-masked hg38; the proxy still denies `ngi-igenomes.s3.amazonaws.com`). Rule C uses minibwa's proper pairs only;
a better pair that neither tool finds is outside any black-box test (that is what the proofs are for).
