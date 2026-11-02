# SAM comparison example

28 read pairs (`ex_R1.fq`, `ex_R2.fq`), run through three tools by `sh Testing/scripts/compare_sam_example.sh`:

| File | From |
|---|---|
| `shim.sam` | `lean-align map shim.idx` (the proved `alignPairs`, formatted by `Spec/Sam.lean`) |
| `bench_pairs.tsv`, `bench_tiers.tsv` | `whole_genome pmap`, mode RTX, `WG_TIEROUT=1`: the found pair, and the router tier / reason |
| `minibwa.sam` | minibwa c07de5c |
| `table.txt` | one row per mate, all of the above side by side |

**The shim is at milestone M1: it reports score bounds only (`XB`, `XT:Z:eachMateUnique` / `boundsOnly`), no
placement. Every pair is unmapped (flags 77 / 141, `*`, POS 0, MAPQ 0).** Compare minibwa against the true positions
and against the bench; the shim columns show what the SAM says today. At M2 (`answerOf` reports the found pair) the
shim column should equal the bench column.

Pairs: 20 mason pairs minibwa maps with MAPQ >= 30 at the true position, one per chromosome (`unique`); 5 mason pairs
with a mate at MAPQ < 30 (`non-unique`); 2 HG002 pairs with both mates unmapped in minibwa and 1 with one mate
unmapped (`unmapped`, `half-mapped`). Picked with `Testing/scripts/sam_example_pick.py`. The truth is in the mason read
name (0-based half-open there, 1-based in the table); HG002 reads are 250 bp and have no truth.

Reading the table:
- `bench=mb`: `same pos` = same chromosome, strand and start; `overlap` = same strand, spans overlap; `no pair` = the
  bench reported no pair (the column after `none` is the router tier and reason, e.g. `T3 tie2`).
- The bench trims both mates with the proved `ReadTrim` first, so its starts can differ by a base or two from
  minibwa's untrimmed alignments. Its penalties (`pen`) are not minibwa's scores.
- The bench reads the FASTA as one record, so it sees the later header lines as letters; the table script undoes
  that shift to give chromosome coordinates.
