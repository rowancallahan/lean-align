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
  /-- The genome allows `getW` (checked once per loop by the compiled loops' dispatchers). -/
  ok : Gt → Bool := fun _ => true
  /-- `get` at a machine-word index, valid when `ok` (`getW_eq`). -/
  getW : Gt → USize → UInt8 := fun g u => get g u.toNat
  getW_eq : ∀ g u, ok g = true → getW g u = get g u.toNat := by intros; rfl

@[reducible] instance : GRead ByteArray where
  get G i := G.get! i
  size G := G.size

@[simp] theorem GRead.get_bytes (G : ByteArray) (i : Nat) : GRead.get G i = G.get! i := rfl
@[simp] theorem GRead.size_bytes (G : ByteArray) : GRead.size G = G.size := rfl
