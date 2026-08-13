import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Finite support classification for unwanted-order index 1.
Only the displayed first-vertex values can satisfy the common-neighbour
predicate for an edge of the required order.  This single certificate
discharges every vacuous fixed-value branch.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def z180K18M12UnwantedCommonPossibleValues1 : Finset Nat :=
  {2, 3, 6, 12, 14, 18, 21, 22, 24, 26,
    33, 34, 38, 39, 42, 46, 48, 51, 54, 57,
    58, 60, 62, 66, 69, 74, 78, 82, 84, 86,
    87, 90, 93, 94, 96, 98, 102, 106, 111, 114,
    118, 120, 122, 123, 126, 129, 132, 134, 138, 141,
    142, 146, 147, 154, 156, 158, 159, 162, 166, 168,
    174, 177, 178}

theorem z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1 :
    ∀ d z : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      Z180K18M12UnwantedCommonNeighbor d z →
      z.val ∈ z180K18M12UnwantedCommonPossibleValues1 := by
  decide

#print axioms z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1

end Fuglede

