import LeanAlign.Cli

/-!
# What is proved about the command line

Check with `lake env lean spec/Cli.lean`.
-/

namespace LeanAlign
namespace Cli

/-- What `parse` returned, unfolded. -/
theorem parse_some {args : List String} {c : Config} (h : parse args = some c) :
    args = [c.input, c.output] ∧ c.input ≠ "" ∧ c.output ≠ "" ∧ c.input ≠ c.output := by
  unfold parse at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      simp_all
  · simp at h

/-- Both paths are command-line arguments, verbatim. -/
theorem parse_paths_mem {args : List String} {c : Config} (h : parse args = some c) :
    c.input ∈ args ∧ c.output ∈ args := by
  rw [(parse_some h).1]; simp

/-- Neither path is empty. -/
theorem parse_paths_ne_empty {args : List String} {c : Config} (h : parse args = some c) :
    c.input ≠ "" ∧ c.output ≠ "" :=
  ⟨(parse_some h).2.1, (parse_some h).2.2.1⟩

/-- The output path is never the input path. -/
theorem parse_input_ne_output {args : List String} {c : Config} (h : parse args = some c) :
    c.input ≠ c.output :=
  (parse_some h).2.2.2

#print axioms parse_some
#print axioms parse_paths_mem
#print axioms parse_paths_ne_empty
#print axioms parse_input_ne_output

end Cli
end LeanAlign
