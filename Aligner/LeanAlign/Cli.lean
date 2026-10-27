/-!
# Command line (pure)

    lean-align <input.seq> <output.tsv>

Theorems about `parse`: `spec/Cli.lean`.
-/

namespace LeanAlign
namespace Cli

structure Config where
  input : String
  output : String

/-- Exactly two arguments: non-empty and different. -/
def parse : List String → Option Config
  | [input, output] =>
    if input == "" || output == "" || input == output then none
    else some { input, output }
  | _ => none

end Cli
end LeanAlign
