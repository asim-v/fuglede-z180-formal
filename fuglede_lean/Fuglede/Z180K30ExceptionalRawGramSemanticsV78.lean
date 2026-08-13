import Fuglede.Z180K30ExceptionalRawGramComplexV76Fix3
import Fuglede.SpectralFourier
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Semantic reflection of the raw K30 Gram data (V78)

This module identifies the exact list-valued raw computation with the usual
complex Fourier matrix.  In particular, for six-tuples `U` and `V`, evaluation
of `gram (List.ofFn U) (List.ofFn V)` is the column Gram matrix of the raw
Fourier matrix, and evaluation of `gramTraceSquare` is the trace of its square.
The final theorem packages these identities, together with the additive Gram
semantics, into `RawFiveGramComplexBridgeV76Fix3`.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators ComplexConjugate
noncomputable section

/-- The standard complex Fourier matrix attached to two raw six-tuples. -/
noncomputable def rawFourierV78
    (U V : Fin 6 → RawPoint) : Matrix (Fin 6) (Fin 6) Complex :=
  fun row column =>
    ZMod.stdAddChar
      (((U row).val : ZMod 36) * ((V column).val : ZMod 36))

@[simp]
theorem rawFourierV78_apply
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    rawFourierV78 U V row column =
      ZMod.stdAddChar
        (((U row).val : ZMod 36) * ((V column).val : ZMod 36)) := rfl

private theorem rawDifference_cast_v78 (left right : RawPoint) :
    ((((left.val + 36 - right.val) % 36 : Nat) : ZMod 36)) =
      (left.val : ZMod 36) - (right.val : ZMod 36) := by
  have hright : right.val ≤ left.val + 36 := by omega
  rw [ZMod.natCast_mod]
  push_cast [hright]
  rw [ZMod.natCast_self]
  ring

private theorem evalCoeffV71Fix_coeffSum_zetaPower_v78
    (exponents : List Nat) :
    evalCoeffV71Fix (coeffSum (exponents.map zetaPower)) =
      (exponents.map fun exponent =>
        ZMod.stdAddChar (exponent : ZMod 36)).sum := by
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · simp only [List.map_map, evalCoeffV71Fix_zetaPower_v76Fix]
  · intro coefficient hcoefficient
    rcases List.mem_map.mp hcoefficient with
      ⟨exponent, _hexponent, rfl⟩
    exact zetaPower_wf_v76Fix exponent

private theorem complex_sum_map_flatMap_v78
    {alpha beta : Type*} (values : List alpha)
    (terms : alpha → List beta) (evaluate : beta → Complex) :
    ((values.flatMap terms).map evaluate).sum =
      (values.map fun value => ((terms value).map evaluate).sum).sum := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

private theorem evalCoeffV71Fix_energy_v78
    (V : RawSet) (difference : Nat) :
    evalCoeffV71Fix (energy V difference) =
      (V.map fun row =>
        (V.map fun column =>
          ZMod.stdAddChar
            (difference *
              ((row.val + 36 - column.val) % 36) : ZMod 36)).sum).sum := by
  unfold energy
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_v78]
    simp only [List.map_map, evalCoeffV71Fix_zetaPower_v76Fix]
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with
      ⟨row, _hrow, hcoefficient⟩
    rcases List.mem_map.mp hcoefficient with
      ⟨column, _hcolumn, rfl⟩
    exact zetaPower_wf_v76Fix _

private theorem evalCoeffV71Fix_gramTraceSquare_explicit_v78
    (U V : RawSet) :
    evalCoeffV71Fix (gramTraceSquare U V) =
      (U.map fun left =>
        (U.map fun right =>
          (V.map fun row =>
            (V.map fun column =>
              ZMod.stdAddChar
                (((left.val + 36 - right.val) % 36) *
                  ((row.val + 36 - column.val) % 36) :
                    ZMod 36)).sum).sum).sum).sum := by
  unfold gramTraceSquare
  rw [evalCoeffV71Fix_coeffSum_v76Fix]
  · rw [complex_sum_map_flatMap_v78]
    simp only [List.map_map, evalCoeffV71Fix_energy_v78]
  · intro coefficient hcoefficient
    rcases List.mem_flatMap.mp hcoefficient with
      ⟨left, _hleft, hcoefficient⟩
    rcases List.mem_map.mp hcoefficient with
      ⟨right, _hright, rfl⟩
    exact energy_wf_v76Fix V _

private theorem gram_ofFn_getD_v78
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    (gram (List.ofFn U) (List.ofFn V)).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero =
      coeffSum ((List.ofFn U).map fun point =>
        zetaPower
          (point.val *
            (((V column).val + 36 - (V row).val) % 36))) := by
  fin_cases row <;> fin_cases column <;>
    simp [gram, rawGramFlatIndexV76Fix3]

private theorem rawCharacter_difference_v78
    (point row column : RawPoint) :
    ZMod.stdAddChar
        (point.val * ((column.val + 36 - row.val) % 36) : ZMod 36) =
      star (ZMod.stdAddChar
          (((point.val : ZMod 36) * (row.val : ZMod 36)))) *
        ZMod.stdAddChar
          (((point.val : ZMod 36) * (column.val : ZMod 36))) := by
  rw [Fuglede.star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  rw [rawDifference_cast_v78]
  ring

/-- Evaluation of the raw Gram list is the analytic column Gram matrix. -/
theorem evalGramV76Fix3_gram_ofFn_v78
    (U V : Fin 6 → RawPoint) :
    evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V)) =
      Matrix.conjTranspose (rawFourierV78 U V) * rawFourierV78 U V := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [evalGramV76Fix3]
  rw [gram_ofFn_getD_v78]
  rw [evalCoeffV71Fix_coeffSum_zetaPower_v78]
  simp only [List.map_map, List.map_ofFn, List.sum_ofFn,
    Matrix.conjTranspose_apply, rawFourierV78_apply]
  apply Finset.sum_congr rfl
  intro point _hpoint
  exact rawCharacter_difference_v78 (U point) (V row) (V column)

private theorem rawFourierGram_apply_v78
    (U V : Fin 6 → RawPoint) (row column : Fin 6) :
    (Matrix.conjTranspose (rawFourierV78 U V) * rawFourierV78 U V)
        row column =
      ∑ point : Fin 6,
        ZMod.stdAddChar
          ((U point).val *
            (((V column).val + 36 - (V row).val) % 36) : ZMod 36) := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro point _hpoint
  simp only [Matrix.conjTranspose_apply, rawFourierV78_apply]
  exact (rawCharacter_difference_v78
    (U point) (V row) (V column)).symm

private theorem raw_trace_character_product_v78
    (left right row column : RawPoint) :
    ZMod.stdAddChar
        (((left.val + 36 - right.val) % 36) *
          ((row.val + 36 - column.val) % 36) : ZMod 36) =
      ZMod.stdAddChar
          (left.val * ((row.val + 36 - column.val) % 36) :
            ZMod 36) *
        ZMod.stdAddChar
          (right.val * ((column.val + 36 - row.val) % 36) :
            ZMod 36) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  rw [rawDifference_cast_v78, rawDifference_cast_v78,
    rawDifference_cast_v78]
  ring

private theorem four_sum_reorder_v78
    (term : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Complex) :
    (∑ left, ∑ right, ∑ row, ∑ column,
        term left right row column) =
      ∑ column, ∑ row, ∑ left, ∑ right,
        term left right row column := by
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

/-- Evaluation of the raw fourth moment is the trace of the squared Gram. -/
theorem evalCoeffV71Fix_gramTraceSquare_ofFn_v78
    (U V : Fin 6 → RawPoint) :
    evalCoeffV71Fix
        (gramTraceSquare (List.ofFn U) (List.ofFn V)) =
      Matrix.trace
        (evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V)) *
          evalGramV76Fix3 (gram (List.ofFn U) (List.ofFn V))) := by
  rw [evalCoeffV71Fix_gramTraceSquare_explicit_v78]
  simp only [List.map_ofFn, List.sum_ofFn]
  rw [evalGramV76Fix3_gram_ofFn_v78]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [rawFourierGram_apply_v78]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [four_sum_reorder_v78]
  apply Finset.sum_congr rfl
  intro column _hcolumn
  apply Finset.sum_congr rfl
  intro row _hrow
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  exact raw_trace_character_product_v78
    (U left) (U right) (V row) (V column)

private theorem getD_mem_of_lt_v78
    {alpha : Type*} (fallback : alpha) (values : List alpha) (index : Nat)
    (hindex : index < values.length) :
    values.getD index fallback ∈ values := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index =>
          have htail : index < tail.length := by simpa using hindex
          simpa using ih index htail

private theorem gramAdd_getD_v78
    (left right : Gram) (index : Nat)
    (hleft : index < left.length) (hright : index < right.length) :
    (gramAdd left right).getD index coeffZero =
      coeffAdd (left.getD index coeffZero) (right.getD index coeffZero) := by
  induction index generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all [gramAdd]
  | succ index ih =>
      cases left <;> cases right <;> simp_all [gramAdd]

private theorem gramAdd_length_v78
    {left right : Gram}
    (hleft : left.length = 36) (hright : right.length = 36) :
    (gramAdd left right).length = 36 := by
  simp [gramAdd, hleft, hright]

private theorem gramAdd_entries_wf_v78
    (left right : Gram)
    (hleft : ∀ coefficient ∈ left, CoeffWF coefficient)
    (hright : ∀ coefficient ∈ right, CoeffWF coefficient) :
    ∀ coefficient ∈ gramAdd left right, CoeffWF coefficient := by
  induction left generalizing right with
  | nil => simp [gramAdd]
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [gramAdd]
      | cons rightHead rightTail =>
          intro coefficient hcoefficient
          simp only [gramAdd, List.zip_cons_cons, List.map_cons,
            List.mem_cons] at hcoefficient
          rcases hcoefficient with hcoefficient | hcoefficient
          · subst coefficient
            apply coeffAdd_wf_v71Fix
            · exact hleft leftHead (by simp)
            · exact hright rightHead (by simp)
          · apply ih rightTail
            · intro c hc
              exact hleft c (by simp [hc])
            · intro c hc
              exact hright c (by simp [hc])
            · exact hcoefficient

private theorem gram_ofFn_length_v78
    (U V : Fin 6 → RawPoint) :
    (gram (List.ofFn U) (List.ofFn V)).length = 36 := by
  simp [gram]

private theorem gramZero_entries_wf_v78 :
    ∀ coefficient ∈ gramZero, CoeffWF coefficient := by
  intro coefficient hcoefficient
  simp [gramZero] at hcoefficient
  subst coefficient
  exact coeffZero_wf_v71Fix

private theorem foldl_gramAdd_invariants_v78
    (values : List Gram) (accumulator : Gram)
    (haccLength : accumulator.length = 36)
    (haccWF : ∀ coefficient ∈ accumulator, CoeffWF coefficient)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    (values.foldl gramAdd accumulator).length = 36 ∧
      ∀ coefficient ∈ values.foldl gramAdd accumulator,
        CoeffWF coefficient := by
  induction values generalizing accumulator with
  | nil => simpa using And.intro haccLength haccWF
  | cons head tail ih =>
      apply ih (gramAdd accumulator head)
      · exact gramAdd_length_v78 haccLength
          (hvalues head (by simp)).1
      · exact gramAdd_entries_wf_v78 accumulator head haccWF
          (hvalues head (by simp)).2
      · intro value hvalue
        exact hvalues value (by simp [hvalue])

private theorem gramSum_invariants_v78
    (values : List Gram)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    (gramSum values).length = 36 ∧
      ∀ coefficient ∈ gramSum values, CoeffWF coefficient := by
  unfold gramSum
  exact foldl_gramAdd_invariants_v78 values gramZero
    (by simp [gramZero]) gramZero_entries_wf_v78 hvalues

private theorem evalGramV76Fix3_gramZero_v78 :
    evalGramV76Fix3 gramZero = 0 := by
  ext row column
  simp [evalGramV76Fix3, gramZero, rawGramFlatIndexV76Fix3,
    evalCoeffV71Fix_coeffZero_v71Fix3]

private theorem evalGramV76Fix3_gramAdd_v78
    (left right : Gram)
    (hleftLength : left.length = 36)
    (hrightLength : right.length = 36)
    (hleftWF : ∀ coefficient ∈ left, CoeffWF coefficient)
    (hrightWF : ∀ coefficient ∈ right, CoeffWF coefficient) :
    evalGramV76Fix3 (gramAdd left right) =
      evalGramV76Fix3 left + evalGramV76Fix3 right := by
  ext row column
  let index := rawGramFlatIndexV76Fix3 row column
  have hindex : index < 36 := by
    dsimp only [index, rawGramFlatIndexV76Fix3]
    omega
  have hleftIndex : index < left.length := by simpa [hleftLength]
  have hrightIndex : index < right.length := by simpa [hrightLength]
  simp only [evalGramV76Fix3, Matrix.add_apply]
  rw [gramAdd_getD_v78 left right index hleftIndex hrightIndex]
  apply evalCoeffV71Fix_coeffAdd_v71Fix3
  · exact hleftWF _ (getD_mem_of_lt_v78
      coeffZero left index hleftIndex)
  · exact hrightWF _ (getD_mem_of_lt_v78
      coeffZero right index hrightIndex)

private theorem evalGramV76Fix3_foldl_gramAdd_v78
    (values : List Gram) (accumulator : Gram)
    (haccLength : accumulator.length = 36)
    (haccWF : ∀ coefficient ∈ accumulator, CoeffWF coefficient)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    evalGramV76Fix3 (values.foldl gramAdd accumulator) =
      evalGramV76Fix3 accumulator +
        (values.map evalGramV76Fix3).sum := by
  induction values generalizing accumulator with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons]
      rw [ih (gramAdd accumulator head)]
      · rw [evalGramV76Fix3_gramAdd_v78 accumulator head]
        simp only [List.map_cons, List.sum_cons]
        abel
        exact haccLength
        exact (hvalues head (by simp)).1
        exact haccWF
        exact (hvalues head (by simp)).2
      · exact gramAdd_length_v78 haccLength
          (hvalues head (by simp)).1
      · exact gramAdd_entries_wf_v78 accumulator head haccWF
          (hvalues head (by simp)).2
      · intro value hvalue
        exact hvalues value (by simp [hvalue])

private theorem evalGramV76Fix3_gramSum_v78
    (values : List Gram)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    evalGramV76Fix3 (gramSum values) =
      (values.map evalGramV76Fix3).sum := by
  unfold gramSum
  rw [evalGramV76Fix3_foldl_gramAdd_v78 values gramZero]
  · rw [evalGramV76Fix3_gramZero_v78]
    simp
  · simp [gramZero]
  · exact gramZero_entries_wf_v78
  · exact hvalues

/-- Canonical complex bridge for five raw six-by-six Gram matrices. -/
noncomputable def rawFiveGramComplexBridgeV76Fix3_ofFn_v78
    (U : Fin 5 → Fin 6 → RawPoint) (V : Fin 6 → RawPoint) :
    RawFiveGramComplexBridgeV76Fix3
      (fun index => List.ofFn (U index)) (List.ofFn V) := by
  let grams : List Gram :=
    List.ofFn fun index : Fin 5 =>
      gram (List.ofFn (U index)) (List.ofFn V)
  have hgrams : ∀ value ∈ grams,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient := by
    intro value hvalue
    rcases List.mem_ofFn.mp hvalue with ⟨index, rfl⟩
    exact ⟨gram_ofFn_length_v78 (U index) V,
      fun coefficient hcoefficient =>
        gram_entry_wf_v76Fix hcoefficient⟩
  refine
    { traceSquare_eval := ?_
      gramSum_eval := ?_
      gramSum_length := ?_
      gramSum_entry_wf := ?_ }
  · intro index
    exact evalCoeffV71Fix_gramTraceSquare_ofFn_v78 (U index) V
  · change evalGramV76Fix3 (gramSum grams) = _
    rw [evalGramV76Fix3_gramSum_v78 grams hgrams]
    simp only [grams, List.map_ofFn, List.sum_ofFn]
  · change (gramSum grams).length = 36
    exact (gramSum_invariants_v78 grams hgrams).1
  · intro row column
    change CoeffWF
      ((gramSum grams).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero)
    have hinvariants := gramSum_invariants_v78 grams hgrams
    apply hinvariants.2
    apply getD_mem_of_lt_v78
    rw [hinvariants.1]
    dsimp only [rawGramFlatIndexV76Fix3]
    omega

theorem rawFiveGramComplexBridgeV76Fix3_ofFn_exists_v78
    (U : Fin 5 → Fin 6 → RawPoint) (V : Fin 6 → RawPoint) :
    RawFiveGramComplexBridgeV76Fix3
      (fun index => List.ofFn (U index)) (List.ofFn V) :=
  rawFiveGramComplexBridgeV76Fix3_ofFn_v78 U V

#print axioms evalGramV76Fix3_gram_ofFn_v78
#print axioms evalCoeffV71Fix_gramTraceSquare_ofFn_v78
#print axioms rawFiveGramComplexBridgeV76Fix3_ofFn_exists_v78

end
end Fuglede.Z180K30ExceptionalRawV2
