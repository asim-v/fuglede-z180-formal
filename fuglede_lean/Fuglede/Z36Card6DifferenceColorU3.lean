import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U3. -/

namespace Fuglede

def U3 : Finset Nat := {3, 6, 12}

def colorU3 (x : ZMod 36) : Fin 3 :=
  ⟨(x.val % 9) / 3, by omega⟩

theorem z36_colorU3_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U3 →
      colorU3 x ≠ colorU3 y := by
  decide

#print axioms z36_colorU3_separation

end Fuglede
