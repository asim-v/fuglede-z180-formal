import Fuglede.Z180K30ExceptionalRawGramComplexV76Fix3
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-!
# Scalar semantics for the raw K30 computation (V78 definitions shard)

This shard contains only the scalar Fourier evaluator and the two exact list
fold identities needed later by the matrix reflection.  Matrix indexing and
the five-Gram bridge are deliberately kept out of this file.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators ComplexConjugate
noncomputable section

/-- The standard complex Fourier matrix attached to two raw six-tuples. -/
noncomputable def rawFourierV78Defs
    (U V : Fin 6 → RawPoint) : Matrix (Fin 6) (Fin 6) Complex :=
  fun row column =>
    ZMod.stdAddChar
      (((U row).val : ZMod 36) * ((V column).val : ZMod 36))

@[simp]
theorem rawFourierV78Defs_apply
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    rawFourierV78Defs U V row column =
      ZMod.stdAddChar
        (((U row).val : ZMod 36) * ((V column).val : ZMod 36)) := rfl

theorem rawDifference_cast_v78Defs (left right : RawPoint) :
    ((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) =
      (left.val : ZMod 36) - (right.val : ZMod 36) := by
  have hright : right.val ≤ left.val + 36 := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub hright]
  norm_num

theorem evalCoeffV71Fix_coeffSum_zetaPower_v78Defs
    (exponents : List Nat) :
    evalCoeffV71Fix (coeffSum (exponents.map zetaPower)) =
      (exponents.map fun exponent =>
        ZMod.stdAddChar (exponent : ZMod 36)).sum := by
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · simp only [List.map_map, Function.comp_apply,
      evalCoeffV71Fix_zetaPower_v76Fix]
  · intro coefficient hcoefficient
    rcases List.mem_map.mp hcoefficient with
      ⟨exponent, _hexponent, rfl⟩
    exact zetaPower_wf_v76Fix exponent

private theorem complex_sum_map_flatMap_v78Defs
    {alpha beta : Type*} (values : List alpha)
    (terms : alpha → List beta) (evaluate : beta → Complex) :
    ((values.flatMap terms).map evaluate).sum =
      (values.map fun value => ((terms value).map evaluate).sum).sum := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

theorem evalCoeffV71Fix_energy_v78Defs
    (V : RawSet) (difference : Nat) :
    evalCoeffV71Fix (energy V difference) =
      (V.map fun row =>
        (V.map fun column =>
          ZMod.stdAddChar
            (((difference : Nat) : ZMod 36) *
              ((((row.val + 36 - column.val) % 36 : Nat)) :
                ZMod 36))).sum).sum := by
  unfold energy
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_v78Defs]
    simp only [List.map_map, Function.comp_apply,
      evalCoeffV71Fix_zetaPower_v76Fix, Nat.cast_mul]
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with
      ⟨row, _hrow, hcoefficient⟩
    rcases List.mem_map.mp hcoefficient with
      ⟨column, _hcolumn, rfl⟩
    exact zetaPower_wf_v76Fix _

theorem evalCoeffV71Fix_gramTraceSquare_explicit_v78Defs
    (U V : RawSet) :
    evalCoeffV71Fix (gramTraceSquare U V) =
      (U.map fun left =>
        (U.map fun right =>
          (V.map fun row =>
            (V.map fun column =>
              ZMod.stdAddChar
                (((((left.val + 36 - right.val) % 36 : Nat)) :
                    ZMod 36) *
                  ((((row.val + 36 - column.val) % 36 : Nat)) :
                    ZMod 36))).sum).sum).sum).sum := by
  unfold gramTraceSquare
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_v78Defs]
    simp only [List.map_map, Function.comp_apply,
      evalCoeffV71Fix_energy_v78Defs, Nat.cast_mul]
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with
      ⟨left, _hleft, hcoefficient⟩
    rcases List.mem_map.mp hcoefficient with
      ⟨right, _hright, rfl⟩
    exact energy_wf_v76Fix V _

#print axioms rawDifference_cast_v78Defs
#print axioms evalCoeffV71Fix_coeffSum_zetaPower_v78Defs
#print axioms evalCoeffV71Fix_energy_v78Defs
#print axioms evalCoeffV71Fix_gramTraceSquare_explicit_v78Defs

end
end Fuglede.Z180K30ExceptionalRawV2
