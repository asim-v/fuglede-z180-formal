import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed neighbor-of-zero color table for maximal allowed order set U5. -/

namespace Fuglede

def U5 : Finset Nat := {2, 6, 9, 36}

def colorU5Neighbor (x : ZMod 36) : Fin 4 :=
  match x.val % 12 with
  | 4 | 6 => 2
  | 5 | 7 => 1
  | 8 => 3
  | _ => 0

theorem z36_colorU5_neighbor_separation :
    ∀ x y : ZMod 36, x ≠ 0 → y ≠ 0 →
      frequencyOrder 36 x ∈ U5 → frequencyOrder 36 y ∈ U5 →
      frequencyOrder 36 (x - y) ∈ U5 →
      colorU5Neighbor x ≠ colorU5Neighbor y := by
  decide

#print axioms z36_colorU5_neighbor_separation

end Fuglede
