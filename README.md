# lean-align

A paired-end short-read aligner written in Lean 4, with a machine-checked proof that every answer
it gives is correct against a small, readable specification.

## Layout

| Folder | What is in it |
|---|---|
| `Spec/` | The specification, frozen (`Spec/FROZEN.sha256`): alignments, genomic placements, the aligner's answers, and the two theorems `alignPairs_correct` and `alignPairs_end_to_end`. |
| `Proofs/` | The same statements with proofs. `Proofs/core/` holds the older internal model (windows, hits, pair specs) that the kernels and router are proved against; `Proofs/Bridge.lean` translates it to `Spec/`. |
| `Aligner/` | The code that runs: alignment `kernels/`, `index/` (minimizer, packed genome, ...), `mapper/` (tier router, pair search), `trimmer/`, and `LeanAlign/` (command line, bytes in / bytes out). |
| `Testing/` | `benches/` (timing and accuracy tools), `scripts/` (checks, simulators), `checks/` (audit), `tests/`, `data/` (download script), `notes/` (design notes, session log). |

`Main.lean` is the executable's entry point: the only file that touches the file system.

## Build and check

```
lake build                                   # everything (Lean 4.35)
bash Testing/bench/verify.sh ~/la-verify     # proofs, axioms, and a small genome mapped identically to minibwa
```

All testing lives in `Testing/bench/` (see its README): `verify.sh` (add `PARANOID=1` for the thorough run, which
ends with `lake check --paranoid`) and `bench.sh` (the benchmark against minibwa).

## For agents

1. `Testing/notes/AGENT_OVERVIEW.md` — start here: current state, rules, where everything lives.
2. `Spec/Aligner.lean` — the top-level statement.
3. `Testing/notes/SESSION_SUMMARY.md` — dated log of decisions and results (read the end first).
