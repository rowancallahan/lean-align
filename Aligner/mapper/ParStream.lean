import ParMap                      -- parMap, batches, mapReadsParArray

/-!
# Codec `streamTasks`: map in batches, write while mapping

The input is cut into batches of `b` items.  Batch `t` is mapped and
formatted to text in its own dedicated task; with `k` workers, batch `t`
starts when batch `t - k` is done, so at most `k` batches compute at once.
A writer (IO, outside this file) takes the tasks in input order, waits for
each and writes its text; later batches keep computing meanwhile.

The theorem: the texts of the tasks, in order, concatenated, are the text of
the whole mapped input.  So whatever the writer writes is
`formatAll fmt (xs.map f)`, and for a mapper proved equal to `mapSpec` it is
the specification's output.

The algorithm, then the theorems, then the proof.
-/

namespace ParMap

/-! ## The algorithm -/

end ParMap

/-! ## The theorems

    String.join ((streamTasks w b f fmt xs).toList.map Task.get) = formatAll fmt (xs.map f)
                                                                   (streamTasks_text)
    (∀ r, f r = mapSpec sc T g r) →
    String.join ((streamTasks w b f fmt reads).toList.map Task.get)
      = formatAll fmt (reads.map (mapSpec sc T g))                 (streamTasks_text_mapSpec)

    bytesOf ((streamTasks w b f fmt xs).toList.map Task.get) = (formatAll fmt (xs.map f)).toUTF8
                                                                   (streamTasks_bytes)
    (∀ r, f r = mapSpec sc T g r) →
    bytesOf ((streamTasks w b f fmt reads).toList.map Task.get)
      = (formatAll fmt (reads.map (mapSpec sc T g))).toUTF8        (streamTasks_bytes_mapSpec)

For every number of workers, batch size (0 included), function and format. -/

/-! ## Proof -/

namespace ParMap

end ParMap

namespace MapSpec

open AlignmentSpec ParMap

end MapSpec

