import Fuglede.Z180K30ExceptionalRawGramSemanticsV78Defs
import Mathlib.Tactic

/-!
# Matrix semantics for the raw K30 Gram computation (V78 Gram shard)

This shard proves only the reflection of one six-by-six raw Gram list into
the analytic Fourier Gram matrix.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators ComplexConjugate
noncomputable section

private theorem gram_ofFn_getD_v78Gram
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V row).val) % 36))) := by
  fin_cases row <;> fin_cases column <;>
    simp [gram, rawGramFlatIndexV76Fix3]

private theorem rawCharacter_difference_v78Gram
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
  rw [rawDifference_cast_v78Defs]
  ring

/-- Evaluation of the raw Gram list is the analytic column Gram matrix. -/
theorem evalGramV76Fix3_gram_ofFn_v78Gram
    (U V : Fin 6 → RawPoint) :
    evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V)) =
      Matrix.conjTranspose (rawFourierV78Defs U V) *
        rawFourierV78Defs U V := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [evalGramV76Fix3]
  rw [gram_ofFn_getD_v78Gram]
  rw [evalCoeffV71Fix_coeffSum_zetaPower_v78Defs]
  simp only [List.map_map, Function.comp_apply, List.map_ofFn,
    List.sum_ofFn, Matrix.conjTranspose_apply,
    rawFourierV78Defs_apply, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro point _hpoint
  exact rawCharacter_difference_v78Gram
    (U point) (V row) (V column)

#print axioms evalGramV76Fix3_gram_ofFn_v78Gram

end
end Fuglede.Z180K30ExceptionalRawV2
