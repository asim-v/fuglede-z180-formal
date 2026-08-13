import Fuglede.Z180K30ExceptionalRawGramSemanticsV78DefsFix
import Mathlib.Tactic

/-! Matrix semantics for one raw six-by-six K30 Gram computation. -/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators ComplexConjugate
noncomputable section

noncomputable def rawFourierV78GramFix
    (U V : Fin 6 → RawPoint) : Matrix (Fin 6) (Fin 6) Complex :=
  fun row column =>
    ZMod.stdAddChar
      (((U row).val : ZMod 36) * ((V column).val : ZMod 36))

@[simp]
theorem rawFourierV78GramFix_apply
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    rawFourierV78GramFix U V row column =
      ZMod.stdAddChar
        (((U row).val : ZMod 36) * ((V column).val : ZMod 36)) := rfl

private theorem gram_ofFn_getD_row_zero_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (0 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (0 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_row_one_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (1 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (1 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_row_two_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (2 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (2 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_row_three_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (3 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (3 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_row_four_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (4 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (4 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_row_five_v78GramFix
    (U V : Fin 6 → RawPoint) (column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 (5 : Fin 6) column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V (5 : Fin 6)).val) % 36))) := by
  fin_cases column <;> simp [gram, rawGramFlatIndexV76Fix3]

private theorem gram_ofFn_getD_v78GramFix
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V row).val) % 36))) := by
  fin_cases row
  · exact gram_ofFn_getD_row_zero_v78GramFix U V column
  · exact gram_ofFn_getD_row_one_v78GramFix U V column
  · exact gram_ofFn_getD_row_two_v78GramFix U V column
  · exact gram_ofFn_getD_row_three_v78GramFix U V column
  · exact gram_ofFn_getD_row_four_v78GramFix U V column
  · exact gram_ofFn_getD_row_five_v78GramFix U V column

private theorem rawCharacter_difference_v78GramFix
    (point row column : RawPoint) :
    ZMod.stdAddChar
        (((point.val : Nat) : ZMod 36) *
          ((((column.val + 36 - row.val) % 36 : Nat)) : ZMod 36)) =
      star (ZMod.stdAddChar
          (((point.val : Nat) : ZMod 36) *
            ((row.val : Nat) : ZMod 36))) *
        ZMod.stdAddChar
          (((point.val : Nat) : ZMod 36) *
            ((column.val : Nat) : ZMod 36)) := by
  rw [Fuglede.star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  rw [rawDifference_cast_v78DefsFix]
  ring

theorem evalGramV76Fix3_gram_ofFn_v78GramFix
    (U V : Fin 6 → RawPoint) :
    evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V)) =
      Matrix.conjTranspose (rawFourierV78GramFix U V) *
        rawFourierV78GramFix U V := by
  ext row column
  change evalCoeffV71Fix
      ((gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero) = _
  rw [Matrix.mul_apply]
  rw [gram_ofFn_getD_v78GramFix]
  calc
    evalCoeffV71Fix
        (coeffSum ((List.ofFn U).map fun point =>
          zetaPower
            (point.val *
              (((V column).val + 36 - (V row).val) % 36)))) =
        (((List.ofFn U).map fun point =>
          ZMod.stdAddChar
            (((point.val *
              (((V column).val + 36 - (V row).val) % 36) : Nat) :
                ZMod 36))).sum) := by
      simpa only [List.map_map, Function.comp_def] using
        evalCoeffV71Fix_coeffSum_zetaPower_v78DefsFix
          ((List.ofFn U).map fun point =>
            point.val *
              (((V column).val + 36 - (V row).val) % 36))
    _ = ∑ point : Fin 6,
        star (rawFourierV78GramFix U V point row) *
          rawFourierV78GramFix U V point column := by
      simp only [List.map_ofFn, List.sum_ofFn,
        rawFourierV78GramFix_apply, Nat.cast_mul]
      apply Finset.sum_congr rfl
      intro point _hpoint
      exact rawCharacter_difference_v78GramFix
        (U point) (V row) (V column)
    _ = ∑ point : Fin 6,
        Matrix.conjTranspose (rawFourierV78GramFix U V) row point *
          rawFourierV78GramFix U V point column := by
      simp only [Matrix.conjTranspose_apply]

#print axioms evalGramV76Fix3_gram_ofFn_v78GramFix

end
end Fuglede.Z180K30ExceptionalRawV2
