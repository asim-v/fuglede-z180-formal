import Fuglede.Z180K30ExceptionalRawGramComplexV76Fix3
import Fuglede.SpectralFourier
import Mathlib.Tactic

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem rawDifference_cast_scratch4 (left right : RawPoint) :
    ((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) =
      (left.val : ZMod 36) - (right.val : ZMod 36) := by
  have hright : right.val ≤ left.val + 36 := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub hright, Nat.cast_add]
  have h36 : ((36 : Nat) : ZMod 36) = 0 := by decide
  rw [h36, add_zero]

private theorem complex_sum_map_flatMap_scratch4
    {alpha beta : Type*} (values : List alpha)
    (terms : alpha → List beta) (evaluate : beta → Complex) :
    ((values.flatMap terms).map evaluate).sum =
      (values.map fun value => ((terms value).map evaluate).sum).sum := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

private theorem evalCoeff_coeffSum_zeta_scratch4
    (exponents : List Nat) :
    evalCoeffV71Fix (coeffSum (exponents.map zetaPower)) =
      (exponents.map fun exponent =>
        ZMod.stdAddChar (exponent : ZMod 36)).sum := by
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · induction exponents with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [evalCoeffV71Fix_zetaPower_v76Fix, ih]
  · intro coefficient hcoefficient
    rcases List.mem_map.mp hcoefficient with ⟨exponent, _hexponent, rfl⟩
    exact zetaPower_wf_v76Fix exponent

private theorem evalCoeff_energy_scratch4
    (V : RawSet) (difference : Nat) :
    evalCoeffV71Fix (energy V difference) =
      (V.map fun row =>
        (V.map fun column =>
          ZMod.stdAddChar
            ((difference : ZMod 36) *
              (((row.val + 36 - column.val) % 36 : Nat) : ZMod 36))).sum).sum := by
  unfold energy
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_scratch4]
    apply congrArg List.sum
    apply List.map_congr_left
    intro row _hrow
    apply congrArg List.sum
    apply List.map_congr_left
    intro column _hcolumn
    change evalCoeffV71Fix
        (zetaPower (difference * ((row.val + 36 - column.val) % 36))) = _
    simpa only [Nat.cast_mul] using
      evalCoeffV71Fix_zetaPower_v76Fix
        (difference * ((row.val + 36 - column.val) % 36))
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with ⟨row, _hrow, hc⟩
    rcases List.mem_map.mp hc with ⟨column, _hcolumn, rfl⟩
    exact zetaPower_wf_v76Fix _

private theorem evalCoeff_trace_scratch4
    (U V : RawSet) :
    evalCoeffV71Fix (gramTraceSquare U V) =
      (U.map fun left =>
        (U.map fun right =>
          (V.map fun row =>
            (V.map fun column =>
              ZMod.stdAddChar
                (((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) *
                  ((((row.val + 36 - column.val) % 36 : Nat) : ZMod 36)))).sum).sum).sum).sum := by
  unfold gramTraceSquare
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_scratch4]
    apply congrArg List.sum
    apply List.map_congr_left
    intro left _hleft
    apply congrArg List.sum
    apply List.map_congr_left
    intro right _hright
    change evalCoeffV71Fix
        (energy V ((left.val + 36 - right.val) % 36)) = _
    exact evalCoeff_energy_scratch4 V
      ((left.val + 36 - right.val) % 36)
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with ⟨left, _hleft, hc⟩
    rcases List.mem_map.mp hc with ⟨right, _hright, rfl⟩
    exact energy_wf_v76Fix V _

end Fuglede.Z180K30ExceptionalRawV2
