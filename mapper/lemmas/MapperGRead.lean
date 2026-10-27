/-!
# Genome letter access

`GRead Gt`: a genome representation with a byte at each index (`get`, 0 past
the end for the byte array) and a length.  The genome-reading kernels take
`{Gt} [GRead Gt] (G : Gt)`; their theorems are stated at `ByteArray`, whose
instance unfolds to `get!` / `size`.  The packed genome (`PGen`,
pool/mapper/MapperPGen.lean) is another instance.
-/

class GRead (Gt : Type) where
  get : Gt → Nat → UInt8
  size : Gt → Nat

@[reducible] instance : GRead ByteArray := ⟨fun G i => G.get! i, fun G => G.size⟩

@[simp] theorem GRead.get_bytes (G : ByteArray) (i : Nat) : GRead.get G i = G.get! i := rfl
@[simp] theorem GRead.size_bytes (G : ByteArray) : GRead.size G = G.size := rfl
