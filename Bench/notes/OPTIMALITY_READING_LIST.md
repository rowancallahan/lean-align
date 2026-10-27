# Optimality-certificate literature: reading list and gap analysis

Compiled 2026-08-21 (agent-assisted survey; links checked at survey time).
Question asked: has anyone machine-checked a theorem of the form "this
machine-code program is within factor x of a proven instruction-count lower
bound"? Companion to the roadmap's optimality annex in SESSION_SUMMARY.md.

## The verdict

**Nobody has the sandwich.** The literature splits into two halves that have
never met: (1) optimality claims without mechanization (superoptimizers,
1987→2025 — search-based, SMT-or-testing-validated, never proof-assistant-
checked); (2) mechanization without ISA-level optimality (proof assistants
hold lower bounds in abstract models and upper bounds down to LLVM IR, never
"program P costs c, every program costs ≥ L, c ≤ x·L" for real machine
code). Negative claim = "no counterexample found after targeted search."

**Bonus verdict for the Sail angle**: nobody in the Sail ecosystem does cost
reasoning at all — the models don't carry timing, and an instruction-count
cost model over a Sail-derived semantics would be new but technically
straightforward. Program-level proofs above Sail models: Islaris (Coq, 2022)
is the state of the art; **a Lean program-logic layer above sail-riscv-lean
does not exist** (independently confirming our harness plan is the gap).
One prior industrial use of the Lean model: Nethermind/Succinct verified the
SP1 zkVM against the Lean-extracted RISC-V spec (2025/26).

## ⭐ The five load-bearing precedents (read these first)

1. **Cruz-Filipe & Schneider-Kamp — Coq-certified sorting-network size
   optimality** (ITP 2015; J. Automated Reasoning 2017). THE template: they
   mechanized the optimality argument and extracted a certified checker that
   validated a ~27 GB SAT-derived non-existence trace, yielding a
   machine-checked "25 comparators is optimal for 9 inputs." The only
   existing machine-checked operation-count optimality theorem — in the
   comparator model, not an ISA. Our sort3 plan = this playbook, applied to
   an ISA. (Paper trail: Codish–Cruz-Filipe–Frank–Schneider-Kamp,
   arXiv:1405.5754 / JCSS 2016 for the SAT result itself.)
2. **Ullrich & Hack — Synthesis of Sorting Kernels (CGO 2025)**. Classical
   A* enumeration with optimality-preserving pruning; beats AlphaDev's
   synthesis time by ~100× on a laptop, **enumerates ALL correct length-3
   x86 sorting kernels (true shortest-kernel optimality for sort3, tool
   level) and a tight lower bound for sort4**. This is EXACTLY the theorem
   we want to mechanize — currently trusted at tool level only. Obvious
   collaboration/target: certify their non-existence side in Lean.
3. **Stoughton et al. — query-model bounds in EasyCrypt** (ITP 2022).
   Mechanized adversary lower bounds AND matching upper bounds in one
   framework (ordered search etc.) — the structural blueprint of the
   sandwich, in an abstract model.
4. **Eberl — comparison-sort lower bound, Isabelle AFP** (2017): ≥ log₂(n!)
   comparisons, mechanized. No Coq or Lean equivalent found → porting it to
   Lean/Mathlib is an open, well-scoped contribution (and a component of any
   sorting-floor argument).
5. **Haslbeck & Lammich — "For a Few Dollars More"** (ESOP 2021 / TOPLAS
   2022): verified fine-grained operation counts refined down to LLVM IR
   (introsort O(n log n) with concrete resource currencies). The deepest
   verified upper-bound cost chain toward machine level.

## Superoptimization (optimal, never machine-checked)

- Massalin 1987 (ASPLOS) — the origin: exhaustive shortest-program search,
  68020/8086 subsets; equivalence by test vectors. NOT AlphaDev — this is
  36 years earlier.
- Bansal & Aiken 2006 (ASPLOS) — brute-force peephole rules, SAT-checked.
- Denali 2002 (PLDI) — "nearly optimal" is the authors' phrase; no formal
  optimality guarantee (treat secondary-source claims as overstated).
- STOKE 2013/2014 (Schkufza–Sharma–Aiken) — MCMC; explicitly NO optimality.
- LENS/GreenThumb 2016 — windowed enumerative+stochastic; optimal within
  window/cost model, SMT-checked.
- Souper — LLVM IR synthesis, per-rewrite SMT equivalence, no optimality.
- Peek (Mullen–Tatlock et al., PLDI 2016) — Coq-VERIFIED peephole
  optimization for CompCert x86: the one place proofs met peepholes, and it
  is correctness-only. Confirms the two halves have only touched there.

## AlphaDev / AlphaEvolve (discovery engines, no proofs, no optimality)

- **AlphaDev** (Mankowitz et al., Nature 2023): AlphaZero-style RL over the
  "AssemblyGame" (append one x86 instruction per move). sort3 = 17 instrs,
  sort4 = 28, sort5 = 43; shipped into LLVM libc++. **Correctness =
  exhaustive TESTING over input orderings** (confirmed via blog + secondary
  sources; Nature paywalled). **No optimality claims** — "shorter than the
  human benchmark," never "shortest." Not the first optimal-assembly
  search (Massalin 1987); real firsts = RL at scale, latency objective,
  production deployment. Follow-ups: Ullrich & Hack CGO 2025 (above);
  "Shorter and faster than Sort3AlphaDev" (arXiv:2307.14503 — also notes
  the blog's sort3 fragment is not a complete sort); no proof-assistant
  coupling found anywhere.
- **AlphaEvolve** (2025): Gemini-based evolutionary search with automated
  evaluators; 4×4 complex matmul in 48 multiplications (first sub-Strassen
  in that setting since 1969). Evaluator-checked, no proofs, no optimality.

## Machine-checked cost bounds (the mechanization half)

- Lower-bound machinery: Eberl (above); Mével–Jourdan–Pottier "Time Credits
  and Time Receipts in Iris" (ESOP 2019) — receipts prove lower bounds on A
  GIVEN program's time (not over all programs — different quantifier than
  our conjectures, but the only ISA-adjacent mechanized lower-bound tech).
- Upper-bound machinery: Charguéraud–Pottier union-find O(α(n)) in Coq;
  Guéneau et al. "A Fistful of Dollars" (ESOP 2018 — formalized big-O) and
  verified incremental cycle detection (ITP 2019); Zhan & Haslbeck IJCAR
  2018; Nipkow et al., "Functional Data Structures and Algorithms" (ACM
  Books 2025 — verified running-time analyses, functional level); RAML/AARA
  (Hoffmann CMU; CAV 2017 adds Coq certificates); calf/decalf (Harper CMU,
  POPL 2022/2024 — cost-aware type theory); TiML (OOPSLA 2017).
- Real machine code: CakeML has verified SPACE cost semantics transferring
  to compiled code (Gómez-Londoño et al., OOPSLA 2020) — no time analog;
  CompCert-verified WCET loop-bound SAFETY (Blazy–Maroneze–Pichardie) — no
  tightness; Myreen's HOL4 machine-code Hoare logic could carry cycle
  counts but no published cost theorems for real programs.
- Complexity theory in provers: Cook-Levin in Coq (Gäher & Kunze, ITP 2021)
  and Isabelle (Balbach, AFP 2023); **no completed Cook-Levin in Lean 4
  found**; Mathlib has Akra-Bazzi + asymptotics.

## Verified assembly (correctness only — performance is never a theorem)

s2n-bignum (HOL Light; now also relational side-channel logic,
arXiv:2505.14348) · Jasmin (EasyCrypt) · Vale (F*) · Fiat-Crypto (Coq,
BoringSSL) · HACL*/EverCrypt (F*) · Bedrock2 (Coq, PLDI 2021) · Islaris
(Iris/Coq over Sail Armv8/RISC-V via Isla, PLDI 2022) · CertiKOS (Coq).
Universal pattern: hand-optimized fast code + machine-checked functional
correctness (+ sometimes constant-time); speed always benchmarked, never
proven.

## Sail ecosystem 2024–26

Sail emits Isabelle/Rocq/Lean (Lean backend new, "highly experimental");
sail-riscv is RISC-V's authoritative spec; Isla (CAV 2021) does SMT
symbolic execution of full ISA specs; CHERI/Morello capability monotonicity
proved in Isabelle over the full ~62k-line model (ESOP 2022, ongoing
Armv9.4 work); **ArchSem (POPL 2026, Rocq)** combines full ISA semantics
with relaxed-memory models — the new frontier for systems-software proofs
above unsimplified architectures (out of our scope: we stay single-hart).

## People / labs (for the blogpost's context section)

Cambridge REMS (Sewell, Armstrong, Bauereiss, Campbell, Pérami — Sail,
Islaris, Morello, ArchSem) · opencompl + Galois (Grosser, Stefanesco et al.
— Sail→Lean) · Chalmers (Myreen, Gómez-Londoño — machine-code logic,
CakeML costs) · SDU (Cruz-Filipe, Schneider-Kamp — THE certified-optimality
precedent) · Ben-Gurion (Codish — SAT sorting networks) · Saarland (Hack,
Ullrich — CGO 2025 optimal kernels; Forster/Kunze line — Coq complexity) ·
Inria (Charguéraud, Pottier, Jourdan, Guéneau — time credits/receipts,
big-O) · TUM (Nipkow; Haslbeck) · Twente (Lammich) · CMU (Hoffmann — RAML;
Harper, Grodin, Niu — calf) · Innsbruck (Eberl) · Stanford (Aiken — STOKE)
· Utah (Regehr — Souper) · IIT Delhi (Bansal) · BU (Stoughton, Gaboardi,
Bun — EasyCrypt query bounds) · UW (Tatlock — Peek) · MIT (Chlipala) ·
DeepMind (Mankowitz — AlphaDev; Novikov — AlphaEvolve; Phothilimthana —
LENS).

## Survey part 2 (2026-08-21): certified giant computation & the race check

**Nobody is racing.** Ullrich & Hack (CGO 2025) has 2 citations, neither
about verification (one tensor-DSL search extension, one RL paper); no
sort5+/other-ISA extensions; no certification attempts by anyone — despite
the group having MetaCoq literacy. The compiler-search community and the
certified-computation community have not met. Instruction-level certified
optimality is unclaimed territory.

**The essay's strongest anecdote — Neri's counterexample**: Cassio Neri,
"Shorter and faster than Sort3AlphaDev" (arXiv:2307.14503) — a
14-instruction sort3 under DIFFERENT I/O conventions vs the "proved
optimal" 17. Optimality claims are meaningless without a machine-checked
spec of the convention; this is spec-fragility in the wild, and exactly
what our statements eliminate.

**The pipeline for big instances already exists (2024–26 Lean wave)**:
- **Keller's conjecture end-to-end in Lean 4** — Gallicchio, Codel, Avigad,
  Heule, ITP 2026: reduction + SAT encoding + symmetry reasoning all
  certified, all dimensions. The current gold standard.
- **Empty Hexagon h(6)=30** — Subercaseaux, Nawrocki, Gallicchio, Codel,
  Carneiro, Heule, ITP 2024 (arXiv:2403.17370): Lean formalizes the
  geometry→CNF reduction (~4.7k lines, ~300 h); UNSAT discharged externally
  by CaDiCaL + cake_lpr (verified checker). The division-of-labor template.
- **LRAT-Catcher** (Szeider, 2026, arXiv:2607.00815): imports SAT
  certificates INTO Lean as theorems by reflection (demoed: Schur S(4),
  R(4,4)). **PBLean** (arXiv:2602.08692): pseudo-Boolean certificates in
  Lean — PB certifies OPTIMALITY, not just UNSAT (VeriPB/Nordström line;
  spreading to MaxSAT, planning).
- Verified checkers: cake_lpr (CakeML→x64, active), lrat_isa (Lammich,
  IJCAR 2024, Isabelle-LLVM), GRAT, CakePB.
- Landmark trust statuses: Pythagorean Triples & Schur 5 =
  verified-checker-validated; packing chromatic ℤ²=15 has a 26-line Python
  encoder as its trust gap (instructive!); Lam's problem found errors in
  BOTH historical searches (the cautionary tale for unverified search);
  Ramsey R(3,8), R(3,9) with verified SAT+CAS certificates (IJCAI 2025).

**Proof of feasible scale — Florath, "A Lean-Certified Proof of
K₈(4,2)=23" (Jun 2026, arXiv:2606.16688)**: an optimal-size covering-code
result, lower bound included, FULLY in Lean 4 with embedded Lean-checked
LRAT refutations, no external solver at replay. One author. The
instruction-level analogue of this is exactly our sort3 flagship, and this
paper proves the scale is a one-person job.

**Open lanes spotted**: optimal addition chains (nothing certified,
nothing even SAT-certificated); Boolean circuit minimality (exact-synthesis
UNSAT sides are lower bounds but nobody archives/validates certificates);
chess tablebases (unverified).

**Natural home / collaborators for the essay & emails**: the Heule–CMU
certified-computation cluster and its Lean orbit — Heule, Subercaseaux,
Gallicchio, Codel, Nawrocki, Avigad, Carneiro (CMU/Lean), Tan (cake_lpr),
Szeider (TU Wien), Nordström's VeriPB group (optimality certificates),
Bright/Ganesh (SAT+CAS). Their 2024–26 arc IS the needed pipeline:
formalize semantics/encoding in Lean → discharge search by cube-and-conquer
→ import certificate as a Lean theorem. The Ullrich–Hack compiler side has
the search and zero certification motion.

## What this changes in our plan

1. **sort3 flagship upgrade**: don't invent our own search — **mechanize
   Ullrich & Hack's CGO 2025 result** (their enumeration already establishes
   tool-level sort3 optimality and a sort4 lower bound; we certify the
   non-existence side in Lean, RISC-V-adapted). The Cruz-Filipe/
   Schneider-Kamp certified-checker pattern is the proof-engineering
   template for validating big search traces.
2. **The blogpost's novelty sentence survives scrutiny**: "every ingredient
   exists separately; nobody has the sandwich for a real ISA" — with this
   file as the citation base.
3. **Free contribution spotted**: port Eberl's comparison-sort lower bound
   to Lean/Mathlib (none exists) — feeds the sorting floors and is a
   standalone Mathlib PR.
4. **Sail cost model**: adding executed-instruction counting over the
   Lean-extracted model is new-but-straightforward — and it is exactly the
   W_P(s) our conjectures quantify; no one else is doing cost over Sail.
