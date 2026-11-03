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
