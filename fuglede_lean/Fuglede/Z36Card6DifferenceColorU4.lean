import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U4. -/

namespace Fuglede

def U4 : Finset Nat := {3, 4, 6}

def colorU4 (x : ZMod 36) : Fin 3 :=
  ⟨(x.val % 18) / 6, by omega⟩

theorem z36_colorU4_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U4 →
      colorU4 x ≠ colorU4 y := by
  decide

#print axioms z36_colorU4_separation

end Fuglede
