import MapSpec
import MapperFastAlgo

namespace MapSpec.Fast

def checkAll (idxs : Array HIdx) (gbs : Array ByteArray) : Bool :=
  idxs.size == gbs.size && (List.range gbs.size).all fun c => checkIdx idxs[c]! gbs[c]!

def mapFast (gbs : Array ByteArray) (idxs : Array HIdx) (R : ByteArray) : Option (Window × Int) :=
  if fastOk R then
    match result (mapChroms R gbs idxs) with
    | some (c, st, len, pen) => some (⟨c, st, len⟩, -(pen : Int))
    | none => none
  else none

end MapSpec.Fast
