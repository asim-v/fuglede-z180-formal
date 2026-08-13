import Fuglede.Z180K30ExceptionalRawGramSemanticsV78GramFix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Trace-square semantics for one raw six-by-six K30 Gram computation. -/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators ComplexConjugate
noncomputable section

private theorem rawCharacter_difference_v78TraceFix
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

private theorem rawFourierGram_apply_v78TraceFix
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    (Matrix.conjTranspose (rawFourierV78GramFix U V) *
        rawFourierV78GramFix U V) row column =
      ∑ point : Fin 6,
        ZMod.stdAddChar
          (((U point).val : ZMod 36) *
            ((((V column).val + 36 - (V row).val) % 36 : Nat) :
              ZMod 36)) := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro point _hpoint
  simp only [Matrix.conjTranspose_apply, rawFourierV78GramFix_apply]
  exact (rawCharacter_difference_v78TraceFix
    (U point) (V row) (V column)).symm

private theorem raw_trace_character_product_v78TraceFix
    (left right row column : RawPoint) :
    ZMod.stdAddChar
        (((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) *
          ((((row.val + 36 - column.val) % 36 : Nat) : ZMod 36))) =
      ZMod.stdAddChar
          (((left.val : Nat) : ZMod 36) *
            ((((row.val + 36 - column.val) % 36 : Nat) : ZMod 36))) *
        ZMod.stdAddChar
          (((right.val : Nat) : ZMod 36) *
            ((((column.val + 36 - row.val) % 36 : Nat) : ZMod 36))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [rawDifference_cast_v78DefsFix, rawDifference_cast_v78DefsFix,
    rawDifference_cast_v78DefsFix]
  ring

private theorem four_sum_reorder_v78TraceFix
    (term : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Complex) :
    (∑ left, ∑ right, ∑ row, ∑ column,
        term left right row column) =
      ∑ column, ∑ row, ∑ left, ∑ right,
        term right left row column := by
  calc
    (∑ left, ∑ right, ∑ row, ∑ column,
        term left right row column) =
        ∑ left, ∑ right, ∑ column, ∑ row,
          term left right row column := by
      apply Finset.sum_congr rfl
      intro left _hleft
      apply Finset.sum_congr rfl
      intro right _hright
      rw [Finset.sum_comm]
    _ = ∑ left, ∑ column, ∑ right, ∑ row,
          term left right row column := by
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.sum_comm]
    _ = ∑ column, ∑ left, ∑ right, ∑ row,
          term left right row column := by
      rw [Finset.sum_comm]
    _ = ∑ column, ∑ left, ∑ row, ∑ right,
          term left right row column := by
      apply Finset.sum_congr rfl
      intro column _hcolumn
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.sum_comm]
    _ = ∑ column, ∑ row, ∑ left, ∑ right,
          term left right row column := by
      apply Finset.sum_congr rfl
      intro column _hcolumn
      rw [Finset.sum_comm]
    _ = ∑ column, ∑ row, ∑ left, ∑ right,
          term right left row column := by
      apply Finset.sum_congr rfl
      intro column _hcolumn
      apply Finset.sum_congr rfl
      intro row _hrow
      rw [Finset.sum_comm]

theorem evalCoeffV71Fix_gramTraceSquare_ofFn_v78TraceFix
    (U V : Fin 6 → RawPoint) :
    evalCoeffV71Fix
        (gramTraceSquare (List.ofFn U) (List.ofFn V)) =
      Matrix.trace
        (evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V)) *
          evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V))) := by
  rw [evalCoeffV71Fix_gramTraceSquare_explicit_v78DefsFix]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [evalGramV76Fix3_gram_ofFn_v78GramFix]
  rw [Matrix.trace]
  change _ = ∑ column : Fin 6, ∑ row : Fin 6,
    (Matrix.conjTranspose (rawFourierV78GramFix U V) *
        rawFourierV78GramFix U V) column row *
      (Matrix.conjTranspose (rawFourierV78GramFix U V) *
        rawFourierV78GramFix U V) row column
  simp_rw [rawFourierGram_apply_v78TraceFix]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [four_sum_reorder_v78TraceFix]
  apply Finset.sum_congr rfl
  intro column _hcolumn
  apply Finset.sum_congr rfl
  intro row _hrow
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  exact raw_trace_character_product_v78TraceFix
    (U right) (U left) (V row) (V column)

#print axioms evalCoeffV71Fix_gramTraceSquare_ofFn_v78TraceFix

end
end Fuglede.Z180K30ExceptionalRawV2
