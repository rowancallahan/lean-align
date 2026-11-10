# How human-specific are the aligner and index? (S-F audit, 2026-11-10, festive 607d16e)

Synthetic genomes only (real genome sites are blocked from the test box). Scripts: Testing/fuzz/gen_genomes.py, genome_audit.py on branch fuzz/harness.

## Generic
- Nothing from hg38 is embedded: the packed genome, minimizer buckets, non-ACGT runs, heavy table and offsets are all computed by buildIndex from the given FASTA. The only built-in sequence is the TruSeq adapter.
- All router budgets are sound for any value (a wrong value costs speed or uniqueness, never correctness).
- Measured on synthetic genomes (20k pairs): bacterium-like 4.6 Mb, yeast-like 13.6 Mb (16 contigs), AT-rich (GC 20%), GC-rich (GC 70%), plant-like 30 Mb with satellites: 95–99.5% proper pairs, 85–92% unique, ~30–40 ms per 1000 pairs. GC extremes change nothing.

## Human-tuned but still works
seedLength 25; gaveUpRepeats 200 / gaveUpSeeds 2; index parameters (k 22, 2^26 buckets, heavy counters); gateBudget 60000, capBudget 5000, joinBudget 20000, shortBudget 1000, walkK 3; scoring 0/−4/−6/−2; junkScore −100; requiredMapBound (4 mismatch-equivalents). All tuned on hg38 reads only; untested on real non-human data.

## Degrades
- Highly repetitive genome (2 kb unit × 2500, 1% divergence): still 99.7% proper pairs, but only 10.7% unique (89% unknown), ~9× slower; it does not give up, it grinds.
- Many contigs: per-pair cost grows with the contig count: 30 contigs 28 ms per 1000 pairs; 30,000 contigs 168 ms; 100,000 contigs ~450 ms. A draft assembly with 100k+ scaffolds would be ~15–20× slower.
- Index size floor: ≥ 276 MB even for a 4.6 Mb genome (fixed 2^26-bucket table).

## Breaks (silently)
- Genomes above ~4.07 Gbp: buildIndex writes a lengths-only record with exit 0; mapping then scans the whole genome (unusable). No error. (From code reading; not run.)
- Lowercase (soft-masked) FASTA: lowercase regions are not indexed: 51% proper pairs instead of 99.4% with half the genome lowercased, no warning. (Measured.)
- Chromosome names with tabs break the .chromosomes file; names keep the whole header line.
- Only forward/reverse proper pairs; TruSeq trimming always on; reads ≤ 1000 bases.
