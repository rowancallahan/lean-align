# A fuzz test you can read in one go: simulate reads, map with both tools, compare

One-time setup (indexes; chr21 is quick): `G` is a one-line-per-chromosome FASTA
(e.g. `awk '/^>/{if(n)print ""; print; n=1; next}{printf "%s", $0} END{print ""}' chr21.fa > G.fa`),
then `lean-align build G.fa shim.idx` and `minibwa index -t 4 G.fa mb`.

The test — four commands (change the seed for a new random test):

    python3 Testing/benches/sim_pairs.py G.fa fz 10000 mason 42          # 10k simulated pairs, origin in each read name
    lean-align map shim.idx fz_R1.fq fz_R2.fq ours.sam 100 1000           # ours
    minibwa map -t 4 mb fz_R1.fq fz_R2.fq > mb.sam                        # minibwa
    python3 Testing/fuzz/compare_sam.py ours.sam mb.sam                   # mate-by-mate comparison

`compare_sam.py` (35 lines) prints up to 10 mates that differ, then: mates, same position (chromosome + POS +
strand), same position + CIGAR, and how many mates each tool places within 10 bp of the true origin (trimming
and minibwa's soft-clipping move POS a little). Modes: `mason` (Illumina-like errors), `low` (HG002-like variants),
`high` (more errors). Expect ours ≈ minibwa on unique reads; differences are mostly minibwa clipping a read end.
