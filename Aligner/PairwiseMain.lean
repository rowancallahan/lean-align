import LeanAlign

/-!
# Command-line entry point

    lean-align <input.seq> <output.tsv>

Every file-system call the tool makes is in `main`: one read of the input,
one existence check of the output path, one exclusive create of the output.
Nothing goes to stdout or stderr.  `Cli.parse` and `run` are pure.

Exit codes: `0` output written; `1` failure, nothing written.
-/

open LeanAlign

/-- Exclusive create (O_EXCL): fails if `path` exists; never overwrites. -/
def writeNewFile (path : System.FilePath) (bytes : ByteArray) : IO Unit :=
  IO.FS.withFile path .writeNew (fun handle => IO.FS.Handle.write handle bytes)

def main (args : List String) : IO UInt32 := do
  let some config := Cli.parse args | return 1
  try
    let inputBytes ← IO.FS.readBinFile config.input
    if ← System.FilePath.pathExists config.output then return 1
    match run scoring inputBytes with
    | .error _ => return 1
    | .ok outputBytes =>
      writeNewFile config.output outputBytes
      return 0
  catch _ => return 1
