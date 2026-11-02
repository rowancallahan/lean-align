# Unique genome: our output vs minibwa where every read has one obvious placement (2026-11-02)

Branch `validate/unique-genome`, based on `claude/festive-fermi-mf9mo6` @ f29c675. No `Spec/` or `Main.lean` edits.
Rerun everything: `MINIBWA=... SAMTOOLS=... bash Testing/unique/run.sh OUTDIR` (about 3 min on 4 cores; genome and
reads are deterministic, md5 checked across two runs).

## Result

On 670 178 pairs (1 340 356 mates) the shim and minibwa c07de5c agree on **every mate**: chromosome, POS, strand,
CIGAR, proper-pair flag, TLEN, and also FLAG, RNEXT, PNEXT, MAPQ (60 both), SEQ, QUAL. Columns 1–11 of
`samtools view` are byte-identical (same md5). Every one of our records says `XU:Z:unique` (`XT:Z:eachMateUnique`).
Both tools are at the true position for every mate. **No differences to categorise.**
Our `AS` is 0 / −4 / −8 for 0 / 1 / 2 substitutions; `samtools calmd` NM on ours equals minibwa's NM on every mate,
and equals the substitution count in the read name.

This is the easy regime by construction; it tests that the plumbing (coordinates, strands, CIGAR, flags, mate
fields, TLEN sign, header) agrees with minibwa, not placement quality on repeats.

## 1. Genome (`Testing/unique/gen_unique_genome.py`)

5 chromosomes `chrU1..chrU5`, 1.2 / 0.9 / 0.8 / 0.6 / 0.5 Mb = 4.0 Mb, uppercase ACGT only. Greedy random walk: each
next base is drawn among those whose new 15-mer is unused; the 15-mer and its reverse complement are then marked
(bitmap of 4^15). Odd k, so no 15-mer is its own reverse complement. No dead end occurred (load 0.75 %). Not in git
(4 MB); the script regenerates it byte for byte (seed 1).

## 2. Proofs (`Testing/unique/UniqueGenome.lean`, lib `UniqueGenome`, a default target; CI_check passes)

No `sorry`, `native_decide`, `implemented_by`, `extern`; `#print axioms`: propext, Classical.choice, Quot.sound only.
Nothing imported (only core Lean).

- `Edits u v n`: Levenshtein script (keep / substitute / delete / insert), `EditDistanceLE u v d := ∃ n ≤ d, Edits u v n`.
  `hamming`: position-wise mismatches.
- `KmersUnique k S`: for strands `S : Array (Array α)`, equal k-mers at (t, i), (t', j) imply t = t' and i = j.
- `windows_far_edits`: `KmersUnique k S`, `(d+1)*k ≤ L`, two whole windows of length L within edit distance d
  ⇒ same strand and `|i − j| ≤ d`.
- `windows_far_hamming`: same hypotheses, Hamming ≤ d ⇒ the same window (t = t', i = j).
- `checkUnique_sound`: the checker (codes of all k-mers, `List.mergeSort`, strictly increasing) returning true
  ⇒ `KmersUnique k S`. Needs no injectivity of the code (equal k-mers ⇒ equal codes); a non-ACGT letter can only
  make it fail.
- `strands g`: strand 2c = chromosome c, 2c+1 = its reverse complement (`strands_forward`, `strands_reverse`).
- `genome_windows_far`: the two statements above for L = 150 and `strands` of a genome the checker accepted.

Two corrections to the task statement:
1. "Any two distinct windows have edit distance > d" is false for small shifts: windows at i and i+1 on one strand
   are always ≤ 2 edits apart. What holds (and is proved) is: within d edits ⇒ same strand and start ≤ d apart;
   with substitutions only, the shift is 0 (`windows_far_hamming`).
2. The bound needed is `(d+1)*k ≤ 150`, weaker than `k ≤ ⌊(150−d)/(d+1)⌋` (an insertion between blocks breaks only one
   block, so the d slack letters are not needed). For k = 15: d = 9 (the task's bound gives d = 8).

So on this genome: two different 150-windows differ in ≥ 10 letters, and any two windows on different strands or
chromosomes, or > 9 apart, are > 9 edits apart. A read with ≤ 2 substitutions is then ≥ 8 substitutions from every
other gapless window and ≥ 8 edits from every placement more than 9 bp away.

Checker run (`lake exe kmer_check unique.fa 15`, `Testing/unique/KmerCheck.lean`, reads the FASTA with the shim's
`Spec.readFasta`): 10 strands, 8 000 000 letters, 7 999 860 15-mers, PASS, 18 s. Controls: a copied 15-mer on another
chromosome, and a 15-mer's reverse complement appended to the same chromosome: both FAIL (exit 1).
Trusted (unproved) here: `readFasta`, the IO in `KmerCheck.lean`, and that the FASTA is the one indexed.

## 3. Reads (`Testing/unique/sim_unique_pairs.py`)

Fragments start every STEP bp on every chromosome; length N(400, 40) clipped to [300, 500] (shim range 100–1000);
each start gives two pairs, R1 on the forward strand and R1 on the reverse strand. 2×150, qualities all `I`
(nothing trimmed). Substitutions per mate cycle (0,0) (1,1) (2,2) (1,0) (0,2) (2,1), at read positions 20–129
(no indels; no clipping incentive). Truth in the name.

| set | STEP / seed | pairs | mates with 0 / 1 / 2 substitutions |
|---|---|---|---|
| sim | 40 / 7 | 199 880 | 133 254 / 133 254 / 133 252 |
| sim2 | 17 / 11 | 470 298 | 313 532 / 313 532 / 313 532 |

## 4. Mapping and comparison (`Testing/unique/compare_unique.py`)

Ours: `lake build`, `lean-align build`, `taskset -c 0-3 lean-align map shim.idx R1 R2 out.sam 100 1000`.
minibwa c07de5c from github.com/lh3/minibwa, `make`, `index -t 4`, `map -t 4` (defaults). Wall: sim 5.2 s vs 2.0 s,
sim2 9.1 s vs 4.2 s (ours includes the 275 MB index read; not a benchmark).

| | sim | sim2 |
|---|---|---|
| mates differing in chrom / POS / strand / CIGAR / proper / TLEN | 0 / 0 / 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 / 0 / 0 |
| mates differing in FLAG / RNEXT / PNEXT / MAPQ / SEQ | 0 / 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 / 0 |
| ours not `XU:Z:unique` | 0 | 0 |
| mates off the truth (either tool, any of the 6 fields) | 0 | 0 |
| minibwa secondary / supplementary records | 0 | 0 |
| FLAGs (both tools) | 99, 147, 83, 163 | same |
| CIGAR (both tools) | 150M only | same |

## 5. samtools 1.24 (htslib/samtools 1.24 release tarballs from GitHub, built without curl/lzma/bz2)

- `quickcheck -v`: exit 0 on ours and minibwa's SAM, both sets.
- `flagstat`: identical files (sim: 399 760 total, 100 % mapped, 100 % properly paired, 0 singletons, 0 secondary/supplementary).
- `view | cut -f1-11`: byte-identical (sim md5 5078694…, sim2 85fcea7…). Only the tags differ: ours `AS XB XU XT`,
  minibwa `NM AS ms md MC MQ`; headers differ in `@HD`/`@PG` (as in OUTPUT_VS_MINIBWA_2026-11.md).
- `sort` + `idxstats`: identical per chromosome (sim: 119 952 / 89 952 / 79 952 / 59 952 / 49 952 mapped).
- `stats` (ours after `calmd`): identical SN lines checked: bases mapped (cigar) 59 964 000, mismatches 399 758,
  error rate 6.667e-3, insert size 399.3 ± 38.6 (sim); sim2 141 089 400, 940 596, 6.667e-3, 399.0 ± 38.5.

## 6. Our BAM writer (`Testing/benches/BamWrite.lean`, `bam_write shim.idx R1 R2 OUT 1 real`)

Both sets: its SAM is byte-identical to the shim's; `samtools quickcheck` exit 0; `samtools view -h OUT.bam` equals the
shim's SAM except the one `@PG ID:samtools` line samtools adds; `bam_check.py` OK (sim 2 032 BGZF blocks, sim2 4 783,
CRC32/ISIZE verified, every record field by field).
