# Real data: lean-align vs minibwa (NovaSeq 200k, HiSeq 200k) — STATUS: BLOCKED, NO RESULTS YET

**No numbers in this note yet.** The script is written and smoke-tested on a hand-made 2-pair SAM only. The run was blocked:

- The permission classifier denied building minibwa c07de5c from the cloned lh3/minibwa source (`make`) and downloading
  elan (needed for Lean v4.35.0, which this box lacks; no `lake`/`lean`/`samtools` either). Not worked around.
- Done before the block: `bench-release` assets for novaseq_200k, hg002_200k, MANIFEST, SHA256, `shim.idx.chromosomes`,
  `mb.l2b` were fetched via `gh api` (works); the minibwa index parts and `shim.idx` parts were still downloading.
  `git clone https://github.com/lh3/minibwa` works; the archive tarball URL gives 403.
- Still needed to get results: (1) permission to build minibwa and install elan/Lean 4.35 + `lake build lean-align` at
  `claude/festive-fermi-mf9mo6` head e384063; (2) the shim index (the release's `shim.idx` was built from an older commit; if the
  head rejects it, rebuild from hg38 `genome.fa`, ~3 GB download).

## Script: `Testing/fuzz/real_vs_minibwa.py SET ours.sam mb.sam [N]`
Writes a markdown report to stdout and `SET.examples.tsv` (raw records of both tools, N=20 each, evenly spread):
1. Per-mate classes: same pos+strand (same CIGAR / CIGAR differs); same diagonal (POS shifted by a leading clip);
   DIFFERENT pos with ours MAPQ 60 and minibwa MAPQ >= 30 (alarming); different pos with either MAPQ 0 (repeats);
   different pos other; mapped by one tool only; unmapped by both; ours degenerate all-insertion (section 1b: minibwa's
   MAPQ / XA / mapped-or-not for those). Different-pos classes also report how many are within 50 bp on the same strand.
2. Score check at the same place: minibwa's score recomputed in our model (0, -4, -(6+2k)) from CIGAR+NM when it has no
   S/H; compared with our AS, split by equal query length vs ours trimmed (SEQ shorter). Counts strictly better / equal /
   worse, gain histogram, and how many are not comparable because minibwa clipped.
3. Pairs minibwa maps with min MAPQ >= 30: our pair score (AS1+AS2) binned (< -100, -100..-50, -50..-32, -32..-16, >= -16), degenerate count, same-place count,
   minibwa's own pair score in our model, cumulative shares below -16/-32/-50/-100, and the number a -50 floor would unmap.
Assumptions to check on the first real run: our AS is the end-to-end penalty of the (trimmed) SEQ; minibwa NM counts N bases as mismatches; our
trimmed mates have no S in CIGAR (trimmed bases are simply absent from SEQ), hence the query-length split.
Example explanations (item 3 of the task) can only be written from the real `examples.tsv`; the `hint` field already flags
minibwa clip, our trimming, XA (repeat), distance, gap-count difference.

Run: `python3 -I Testing/fuzz/real_vs_minibwa.py novaseq_200k ours.sam mb.sam`, with the SAMs from the commands in
`Testing/scripts/output_vs_minibwa.sh` (`lean-align map shim.idx R1 R2 ours.sam 100 1000`; `minibwa map -t 4 mb R1 R2`).
