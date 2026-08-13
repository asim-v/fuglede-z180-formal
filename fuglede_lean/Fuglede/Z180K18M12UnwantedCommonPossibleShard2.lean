import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Finite support classification for unwanted-order index 2.
Only the displayed first-vertex values can satisfy the common-neighbour
predicate for an edge of the required order.  This single certificate
discharges every vacuous fixed-value branch.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def z180K18M12UnwantedCommonPossibleValues2 : Finset Nat :=
  {3, 6, 12, 18, 21, 24, 33, 39, 42, 48,
    51, 54, 57, 60, 66, 69, 78, 84, 87, 90,
    93, 96, 102, 111, 114, 120, 123, 126, 129, 132,
    138, 141, 147, 156, 159, 162, 168, 174, 177}

theorem z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2 :
    ∀ d z : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      Z180K18M12UnwantedCommonNeighbor d z →
      z.val ∈ z180K18M12UnwantedCommonPossibleValues2 := by
  decide

#print axioms z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2

end Fuglede

