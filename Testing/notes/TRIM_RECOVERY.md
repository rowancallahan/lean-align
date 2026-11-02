# Trimming recovery on hg38 (`speed/n31-repeat-hint`)

Question (parent, from O3/O4): of the pairs where a mate has no hit within cap −16 (bound −17), how many get a hit after
the proved `ReadTrim` (quality/adapter end trimming) is applied to the mates? Measurement only; no Spec/Shim/Main change.

Method: the same 200k pairs through bench RTX (`WG_XH=0`, 4 cores, `WG_TIEROUT=1`, hg38 bench index), once **untrimmed**
(`>name`/sequence input, which the bench does not trim) and once as **FASTQ** (trimmed by `ReadTrim.trimReadQ`, neutral
quality `defQ`; this is the bench's and the shim's normal path). Per pair, "no hit within the cap" = RT reason `noHit1/2`.
Dumps compared pair by pair.

## Counts
| | HiSeq (hg002_200k) | NovaSeq (novaseq_200k) |
|---|---|---|
| untrimmed: pairs with a mate without a hit (`noHit`) | **39,299** | **16,735** |
| untrimmed: T3 pairs with bound 17 | 13,300 | 6,768 |
| pairs mapped (kept), untrimmed → trimmed | 141,438 → 164,485 (+23,047) | 164,120 → 165,204 (+1,084) |
| those `noHit` pairs, after trim: still `noHit` | 15,191 (38.7%) | 10,730 (64.1%) |
| …a hit now (reason `gated`, router goes on) | 14,635 | 1,516 |
| …tie (hits, not unique) | 2,946 | 287 |
| …`noPartner` / `notProper` (hits, no proper partner) | 2,261 / 61 | 867 / 3 |
| …`short` (trimmed mate too short to search) | 4,205 | 3,332 |
| final tag of the pairs no longer `noHit`: T1 / T1u / T1um / T2 / T2b | 13,707 / 208 / 158 / 1,880 / 11 | 917 / 79 / 26 / 450 / 11 |
| final tag T3 of those (mapped nowhere for another reason) | 8,144 | 4,522 |
| new `noHit` pairs only after trimming | 592 | 1,692 |

So trimming gives a hit to **19,903 of 39.3k HiSeq `noHit` pairs (gated + tie + noPartner + notProper, 50.6%)** and
**2,673 of 16.7k NovaSeq (16.0%)**; 15,964 (HiSeq, 40.6%) and 1,483 (NovaSeq, 8.9%) end up mapped (T1/T1u/T1um/T2/T2b).
NovaSeq's `noHit` pairs are mostly not an end-quality problem (64% stay `noHit`; 20% become too short).

## CPU cost of trimming (one thread, 200k pairs, median of 3)
Time to read the mates in the bench (`mates read` line, new): untrimmed text 2.91 s (HiSeq), 1.85 s (NovaSeq);
FASTQ plus `trimReadQ` 8.02 s and 5.33 s. Difference **≈ 5.1 s (HiSeq) and 3.5 s (NovaSeq) of one thread per 200k pairs**; it
includes parsing the quality lines, so it overstates `trimReadQ` itself. Against bench mapping CPU of 21 s (HiSeq, 4 cores) this is
serial work in the bench (the shim trims inside its chunk workers).
