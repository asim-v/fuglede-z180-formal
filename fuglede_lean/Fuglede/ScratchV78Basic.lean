import Fuglede.Z180K30ExceptionalRawGramComplexV76Fix3
import Fuglede.SpectralFourier
import Mathlib.Tactic

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem rawDifference_cast_scratch (left right : RawPoint) :
    ((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) =
      (left.val : ZMod 36) - (right.val : ZMod 36) := by
  have hright : right.val ≤ left.val + 36 := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub hright]
  norm_num

private theorem evalCoeff_coeffSum_zeta_scratch
    (exponents : List Nat) :
    evalCoeffV71Fix (coeffSum (exponents.map zetaPower)) =
      (exponents.map fun exponent =>
        ZMod.stdAddChar (exponent : ZMod 36)).sum := by
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · simp only [List.map_map, Function.comp_apply,
      evalCoeffV71Fix_zetaPower_v76Fix]
  · intro coefficient hcoefficient
    rcases List.mem_map.mp hcoefficient with ⟨exponent, _hexponent, rfl⟩
    exact zetaPower_wf_v76Fix exponent

example (V : RawSet) (difference : Nat) :
    evalCoeffV71Fix (energy V difference) =
      (V.map fun row =>
        (V.map fun column =>
          ZMod.stdAddChar
            ((difference : ZMod 36) *
              (((row.val + 36 - column.val) % 36 : Nat) : ZMod 36))).sum).sum := by
  unfold energy
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_apply,
      evalCoeffV71Fix_zetaPower_v76Fix, List.sum_flatten]
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with ⟨row, _hrow, hc⟩
    rcases List.mem_map.mp hc with ⟨column, _hcolumn, rfl⟩
    exact zetaPower_wf_v76Fix _

end Fuglede.Z180K30ExceptionalRawV2
