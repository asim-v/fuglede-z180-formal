import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U9. -/

namespace Fuglede

def U9 : Finset Nat := {2, 3, 4}

def colorU9 (x : ZMod 36) : Fin 4 :=
  ⟨x.val / 9, by
    have hx := x.val_lt
    omega⟩

theorem z36_colorU9_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U9 →
      colorU9 x ≠ colorU9 y := by
  decide

#print axioms z36_colorU9_separation

end Fuglede
