# Accuracy on reads from the real mason2 simulator (10,000 hg38 pairs)

Simulator: `mason_simulator version: 2.0.9 [tarball]`, SeqAn 2.4.0, from the Ubuntu 24.04 package `seqan-apps` 2.4.0+dfsg-16 (`apt-get install seqan-apps`; binary `/usr/lib/seqan/bin/mason_simulator`, not on PATH).
Command (genome = hg38.upper.fa, multi-line FASTA; a `genome.fa.fai` is written next to it on first use; 69 s, 0.62 GB peak RSS):

    mason_simulator -ir genome.fa -n 10000 -o R1.fq -or R2.fq -oa truth.sam --seed 1 --illumina-read-length 150 --illumina-prob-mismatch-scale 2.5

Names `simulated.<n>/1`, `/2`; truth.sam: one SAM record per mate, QNAME `simulated.<n>`, FLAG 99/147/83/163 (mate = FLAG&64 ? 1 : 2), POS+CIGAR = true place, MAPQ 255. Fragments: normal, mean 300, sd 30 (defaults; true inserts 225..418 here).
Mapped with lean-align (festive code = cc26db2, hg38 ic.idx; `map idx R1 R2 ours.sam 100 1000`) and minibwa c07de5c (`map -t 4`). `score.py DIR GENOME_FA` reproduces `score_output.txt` from truth.sam, ours.sam, mb.sam.
Overlap rule (the minibwa paper's): a mate is correct if same chromosome and |A∩B|/|A∪B| >= 10% of the mapped and the true interval; a pair is correct if both mates are.

| 10,000 pairs | lean-align | minibwa |
|---|---|---|
| both mates mapped | 98.15% | 100.00% |
| pair-correct, overlap rule | 94.98% | 97.89% |
| pair-correct, both starts within 10 bp | 87.16% | 97.88% |
| no N in either mate (8,019 pairs): overlap rule | 95.19% | 97.87% |
| an N in a mate (1,981 pairs): overlap rule | 94.14% | 97.98% |
| an N in a mate: starts within 10 bp | 54.67% | 97.98% |

The start-within-10-bp rule counts a trimmed mate (our POS is the start of the trimmed window) as wrong; use the overlap rule.
N letters: 2,234 N in the reads (R1 1,083), 1 of them at a reference N at the true position; the FASTA has no lower-case letters. `mason_simulator --help` has no N-probability option; the N qualities are not Q0 and they pile up at the 3' end (R1: 457 of 1,083 in positions 125-149), so they look like substitutions of the Illumina error model (inference, not documented).
Wrong reads at our MAPQ 60: 2 reads, one pair (simulated.4253, proper pair, XU unique, AS 0): see score_output.txt. Spec scoring of our windows (read aligned end to end): at the true place -4 in total, at ours 0, so the true placement scores strictly worse and the unique claim is not contradicted.
