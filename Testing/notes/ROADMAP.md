# Roadmap after the short-read release (Rowan, 2026-11-10)

Plan only. Nothing here is started. Spec changes are Rowan's.

## Order
1. Refactor the Spec into one Spec with a settings record. Short-read DNA is the first instance.
2. RNA-seq (splice-aware), compared against STAR.
3. HiFi long reads.
4. Nanopore (high error) long reads. Long-term. Compared against minimap2.

## Settings record (numbers only)
- mismatch cost, gap costs (maybe two-piece for long reads)
- optional intron: cost by splice motif, min and max length
- optional pairing: orientation, distance range
- thresholds (required bound, junk score) as a function of read length
- clipping cost per clipped letter or end; infinity = end-to-end

## Decisions to make in the Spec
- Local alignment: keep match = 0 and add a clipping cost. A positive match score would change what every score means.
- RNA-seq: a zero-cost intron makes the best alignment degenerate. Needs a positive intron cost, a minimum exon piece length, or both. Proper-pair distance grows to about 1 Mb. SAM needs CIGAR N and a strand tag.
- Long reads: no mates; correctness for one read; thresholds scale with length; PAF output spec (or SAM); end-to-end vs clipped/split reads.
- Nanopore: exact seeds rarely give a bound at 5% error, so few reads will be proved unique. Accepted: the goal there is faster than minimap2 with the proved cases as a bonus.

## Targets for an agent swarm
- Fixed Spec, an evaluation harness, and a speed target.
- The target needs an accuracy floor (for example % of simulated reads at the true position, % of junctions found), because the Spec allows `unknown` and unmapped answers and speed work will use that room.
- Proof cost below the Spec is not a constraint.
