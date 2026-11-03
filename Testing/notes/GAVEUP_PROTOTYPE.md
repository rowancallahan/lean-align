# `.gaveUp` prototype (`proof/gaveup`, off 3db69c7; NOT for Rowan's Spec)

## Spec copy (this branch only; Spec/FROZEN.sha256 regenerated here)
`seedLength = 25`, `gaveUpRepeats = 500`, `Genome.occurrences` (windows equal to the word or its reverse complement,
all starts of all chromosomes), `Genome.RepeatWitness` (a 25-letter window of the read occurring ≥ 500 times),
`Uniqueness.gaveUp` with `| .gaveUp => answer.found = none ∧ (RepeatWitness mate1 ∨ RepeatWitness mate2)`.
Mirrored in Proofs/Answer.lean; `uniquenessText` prints `gaveUp` (Spec/Sam + Proofs/Sam); `CorrectU`'s arm is
`found = none`.

## Proof side
- The lemma as first proposed (bucket size = occurrences) does not hold: the index is a minimizer index (k 22, w 4),
  a bucket is a hash prefix of the 22-word, so it is only an upper bound. Used instead: the existing exact lookup
  theorem `Mz.lookupSeed_mem` (places of the 25-letter seed in the whole packed genome, strictly increasing).
- `GaveUp.repeatMate` (Proofs/GaveUp.lean): seeds at `0, 25, 50, …`; a place counts when it lies inside one
  chromosome (chromosome guessed by binary search over `offs`, then checked). Counted places are distinct
  `(chromosome, start)` windows equal to the seed, hence `≤ occurrences` (`count_le_occurrences`, own nodup-sublist
  lemma; core has no `Nodup.subperm`). Forward strand only (a lower bound). `repeatMate_sound`: standard axioms.
- `answerOfReads`: a leftover with `gaveUpOn && (repeatMate mate1 || repeatMate mate2)` answers
  `{ a with uniqueness := .gaveUp }` (keeps the leftover's proved bound) instead of the second look.
  `alignPairs_correct` / `alignPairs_end_to_end`: standard axioms. FUZZ=1 CI_check passes.

## Measured (hg38, 4 threads, 200k pairs; base = 3db69c7)
| set | gaveUp pairs | wall base → new | mapped base → new | at truth base → new |
|---|---|---|---|---|
| mason | 2,273 (1.1%) | 185.6 → 17.3 s | 193,629 → 192,382 | 188,245 → 187,401 |
| low | 1,184 (0.6%) | 201.8 → 13.3 s | 199,428 → 198,321 | 193,861 → 193,051 |
The second look on repeat leftovers is what makes 3db69c7 slow on the sims (cpu 437 / 630 s); gaveUp removes that
but loses the pairs the second look found (mason −1,247 mapped, −844 at truth; low −1,107 / −810).

NovaSeq / HiSeq: not measurable on 3db69c7 here. Both base and new are killed (out of memory, 13.96 GB) on a single
low-quality NovaSeq pair (`A00744:46:HV3C3DSXX:2:1103:27218:22420`, mostly Q11): probably mates trimmed below 25
letters, whose second look scans the genome window by window (`hitsKPF` fallback). gaveUp cannot cover it (no
25-letter seed). This is a 3db69c7 problem, independent of the prototype.

## On the merged base 1266f07 (minLength 25; rebased, `afterLeftover` shared by `answerOfReads` and `alignOneP`)
CI + FUZZ green (435 theorems). The OOM pair now runs: base 30.5 s, prototype 1.9 s (5.2 GB).

| set (200k pairs, 4 threads) | gaveUp pairs | wall base → new | CPU base → new | mapped base → new | unique |
|---|---|---|---|---|---|
| NovaSeq | 3,356 | 313.8 → 15.1 s | 873.1 → 44.5 s | 187,221 → 186,189 | 164,839 both |
| HiSeq | 2,520 | 119.6 → 12.5 s | 298.5 → 38.4 s | 186,498 → 185,804 | 169,101 both |

## Rowan's K question: gave-up pairs with ≥ K grid seeds (offsets 0, 25, …) of ≥ 500 in-chromosome hits
(Testing/benches/GaveUpK.lean; trimmed mates; pair = either mate)
| set | gave up | K=1 m1 / m2 / pair | K=2 m1 / m2 / pair | K=3 m1 / m2 / pair |
|---|---|---|---|---|
| mason (3db69c7) | 2,273 | 1,591 / 1,537 / 2,273 | 1,236 / 1,158 / 1,928 (85%) | 885 / 797 / 1,488 (65%) |
| low (3db69c7) | 1,184 | 833 / 748 / 1,184 | 705 / 609 / 1,077 (91%) | 628 / 495 / 980 (83%) |
| NovaSeq | 3,356 | 2,335 / 2,000 / 3,356 | 1,356 / 1,094 / 2,096 (62%) | 931 / 666 / 1,419 (42%) |
| HiSeq | 2,520 | 1,765 / 1,502 / 2,520 | 1,009 / 918 / 1,688 (67%) | 714 / 618 / 1,223 (49%) |

Pairs failing K = 2 (would get the second look): base maps / at truth, and the second look's CPU on them (min CPU of 3
warm runs, base − prototype on the subset; the VM's load time makes small numbers noisy):
| set | K=2 fails | second look maps | at truth | CPU cost | vs. gaveUp's total saving |
|---|---|---|---|---|---|
| mason | 345 | 116 | 77 | ~3.6 s | ~395 s |
| low | 107 | 97 | 69 | ~2.0 s | ~600 s |
| NovaSeq | 1,260 | 143 (all ≥ −50, none unique) | – | ~20 s | ~829 s |
| HiSeq | 832 | 119 (all ≥ −50, none unique) | – | ~18 s | ~260 s |

## K = 2 option (`gaveUpSeeds`, prototype Spec default 2)
Spec copy (PROTOTYPE, not Rowan's): `gaveUpSeeds : Nat := 2`; `RepeatWitness` = a list of `gaveUpSeeds` starts,
pairwise non-overlapping (`a + seedLength ≤ b`), each window occurring ≥ `gaveUpRepeats` times. `repeatSeeds` lists
the mate's grid seeds with ≥ 500 in-chromosome hits; `repeatMate` = `gaveUpSeeds ≤ length`. `seed_sound` (one seed) +
`repeatMate_sound` (the first `gaveUpSeeds` of them: grid starts are 25 apart). CI + FUZZ green, standard axioms.
NovaSeq 200k (one run): gaveUp 2,096 pairs (as predicted), mapped 186,332 (+143 vs K = 1), unique unchanged,
wall 26.3 s / CPU 83.1 s (K = 1: 15.1 / 44.5 s; one run each, load noise included).
