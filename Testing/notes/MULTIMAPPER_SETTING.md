# Proposal: a "multimappers" setting (n29-heur, 2026-10-29) — not implemented, Spec/ untouched

Rowan's ask: a setting to choose between "don't map multimappers" and "report one placement".

## What the Spec already says
`PairAnswer` (Spec/Aligner.lean) already has `uniqueness = .multimapper` with `found = some report`
(one of the tied best proper pairs) and `Correct` already proves that it is a best proper pair and
that another best proper pair at other placements exists. So "report one placement" needs no new
claim: it is what `.multimapper` means. The missing piece is only (a) the router producing such
answers more often (T1um today proves a tie but keeps no pair) and (b) how the shim prints them.

## Proposal
1. **The setting is output policy, not a correctness claim.** Add to `InsertSettings` (or a new
   `ReportSettings` next to it) a field
   `multimappers : MultiPolicy := .reportOne` with `inductive MultiPolicy | reportOne | unmapped`.
   `PairAnswer.Correct` does not mention it: with `.unmapped`, `alignPairs` may still return the
   proved `.multimapper` answer, and only `samChunk` (trusted formatting, Spec/Sam.lean) prints the
   pair as unmapped (flag 4/8, XU:Z:multimapper, XB kept). This keeps the theorem unchanged and puts
   the choice where MAPQ already lives (`mapq`: 60 unique, else 0).
2. **Alternative, if the policy must be in the proved part:** add to `PairAnswer.Correct` the
   conjunct `settings.multimappers = .unmapped → answer.uniqueness = .multimapper → answer.found = none`
   — but `.multimapper`'s clause requires `found = some`, so this needs `.multimapper` split into
   "proved tie, pair reported" and "proved tie, pair withheld" (a new `Uniqueness` constructor,
   e.g. `tieWithheld`, whose clause is the tie existence without a report). More Spec change for no
   extra guarantee; option 1 is preferred.
3. **Search consequence (unproved side, free to change):** with `.reportOne` the router may stop at
   the first proved tie (any proper pair reaching the proved bound plus one other placement); with
   `.unmapped` it may stop as soon as a tie is proved, without building the CIGAR. Neither needs a
   new proof: both stop points are already `.multimapper` answers that the checker verifies.
4. **Shim/CLI:** one flag (e.g. `--multimappers=one|none`, default `one`) parsed in Spec/Shim.lean
   (trusted plumbing) and passed to `samChunk`.

Decision for Rowan: option 1 (formatting only, no theorem change) vs option 2 (in the theorem).
