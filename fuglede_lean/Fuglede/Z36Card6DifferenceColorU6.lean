import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Fixed proper-color table for maximal allowed order set U6. -/

namespace Fuglede

def U6 : Finset Nat := {2, 4, 6, 12, 18, 36}

def colorU6 (x : ZMod 36) : Fin 4 :=
  ⟨x.val % 4, Nat.mod_lt _ (by norm_num)⟩

theorem z36_colorU6_separation :
    ∀ x y : ZMod 36, x ≠ y → frequencyOrder 36 (x - y) ∈ U6 →
      colorU6 x ≠ colorU6 y := by
  decide

#print axioms z36_colorU6_separation

end Fuglede
