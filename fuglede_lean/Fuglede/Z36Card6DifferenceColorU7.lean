import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U7. -/

namespace Fuglede

def U7 : Finset Nat := {2, 4, 6, 9, 12}

def colorU7 (x : ZMod 36) : Fin 4 :=
  ⟨(x.val % 12) / 3, by omega⟩

theorem z36_colorU7_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U7 →
      colorU7 x ≠ colorU7 y := by
  decide

#print axioms z36_colorU7_separation

end Fuglede
