import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed neighbor-of-zero color table for maximal allowed order set U8. -/

namespace Fuglede

def U8 : Finset Nat := {2, 3, 12}

def colorU8Neighbor (x : ZMod 36) : Fin 4 :=
  match x.val with
  | 12 | 18 => 2
  | 15 | 21 => 1
  | 24 => 3
  | _ => 0

theorem z36_colorU8_neighbor_separation :
    ∀ x y : ZMod 36, x ≠ 0 → y ≠ 0 →
      frequencyOrder 36 x ∈ U8 → frequencyOrder 36 y ∈ U8 →
      frequencyOrder 36 (x - y) ∈ U8 →
      colorU8Neighbor x ≠ colorU8Neighbor y := by
  decide

#print axioms z36_colorU8_neighbor_separation

end Fuglede
