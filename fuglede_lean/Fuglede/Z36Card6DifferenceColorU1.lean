import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U1. -/

namespace Fuglede

def U1 : Finset Nat := {9, 18, 36}

def colorU1 (x : ZMod 36) : Fin 3 :=
  ⟨x.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem z36_colorU1_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U1 →
      colorU1 x ≠ colorU1 y := by
  decide

#print axioms z36_colorU1_separation

end Fuglede
