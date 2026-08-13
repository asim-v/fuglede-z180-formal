import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U2. -/

namespace Fuglede

def U2 : Finset Nat := {4, 9, 12, 18}

def colorU2 (x : ZMod 36) : Fin 3 :=
  ⟨(x.val % 6) / 2, by omega⟩

theorem z36_colorU2_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U2 →
      colorU2 x ≠ colorU2 y := by
  decide

#print axioms z36_colorU2_separation

end Fuglede
