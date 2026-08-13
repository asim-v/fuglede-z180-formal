import Fuglede.Z180K30ExceptionalRawGramSemanticsV78TraceFix
import Mathlib.Tactic

/-! Additive five-Gram semantics for the exact raw K30 certificate. -/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators
noncomputable section

private theorem getD_mem_of_lt_v78AggregateFix
    {α : Type*} (fallback : α) (values : List α) (index : Nat)
    (hindex : index < values.length) :
    values.getD index fallback ∈ values := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index =>
          have htail : index < tail.length := by simpa using hindex
          exact List.mem_cons_of_mem head (ih index htail)

private theorem gramAdd_getD_v78AggregateFix
    (left right : Gram) (index : Nat)
    (hleft : index < left.length) (hright : index < right.length) :
    (gramAdd left right).getD index coeffZero =
      coeffAdd (left.getD index coeffZero)
        (right.getD index coeffZero) := by
  induction index generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all [gramAdd]
  | succ index ih =>
      cases left <;> cases right <;> simp_all [gramAdd]

private theorem gramAdd_length_v78AggregateFix
    {left right : Gram}
    (hleft : left.length = 36) (hright : right.length = 36) :
    (gramAdd left right).length = 36 := by
  simp [gramAdd, hleft, hright]

private theorem gramAdd_entries_wf_v78AggregateFix
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
            exact coeffAdd_wf_v71Fix
              (hleft leftHead (by simp))
              (hright rightHead (by simp))
          · apply ih rightTail
            · intro c hc
              exact hleft c (by simp [hc])
            · intro c hc
              exact hright c (by simp [hc])
            · exact hcoefficient

private theorem gram_ofFn_length_v78AggregateFix
    (U V : Fin 6 → RawPoint) :
    (gram (List.ofFn U) (List.ofFn V)).length = 36 := by
  simp [gram]

private theorem gramZero_entries_wf_v78AggregateFix :
    ∀ coefficient ∈ gramZero, CoeffWF coefficient := by
  intro coefficient hcoefficient
  simp [gramZero] at hcoefficient
  subst coefficient
  exact coeffZero_wf_v71Fix

private theorem foldl_gramAdd_invariants_v78AggregateFix
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
      · exact gramAdd_length_v78AggregateFix haccLength
          (hvalues head (by simp)).1
      · exact gramAdd_entries_wf_v78AggregateFix accumulator head haccWF
          (hvalues head (by simp)).2
      · intro value hvalue
        exact hvalues value (by simp [hvalue])

private theorem gramSum_invariants_v78AggregateFix
    (values : List Gram)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    (gramSum values).length = 36 ∧
      ∀ coefficient ∈ gramSum values, CoeffWF coefficient := by
  unfold gramSum
  exact foldl_gramAdd_invariants_v78AggregateFix
    values gramZero
    (by simp [gramZero])
    gramZero_entries_wf_v78AggregateFix
    hvalues

private theorem evalGramV76Fix3_gramZero_v78AggregateFix :
    evalGramV76Fix3 gramZero = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [evalGramV76Fix3, gramZero, rawGramFlatIndexV76Fix3,
      evalCoeffV71Fix_coeffZero_v71Fix3]

private theorem evalGramV76Fix3_gramAdd_v78AggregateFix
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
  have hleftIndex : index < left.length := by
    simpa [hleftLength] using hindex
  have hrightIndex : index < right.length := by
    simpa [hrightLength] using hindex
  simp only [evalGramV76Fix3, Matrix.add_apply]
  rw [gramAdd_getD_v78AggregateFix
    left right index hleftIndex hrightIndex]
  apply evalCoeffV71Fix_coeffAdd_v71Fix3
  · exact hleftWF _
      (getD_mem_of_lt_v78AggregateFix
        coeffZero left index hleftIndex)
  · exact hrightWF _
      (getD_mem_of_lt_v78AggregateFix
        coeffZero right index hrightIndex)

private theorem evalGramV76Fix3_foldl_gramAdd_v78AggregateFix
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
      · rw [evalGramV76Fix3_gramAdd_v78AggregateFix accumulator head]
        simp only [List.map_cons, List.sum_cons]
        abel
        exact haccLength
        exact (hvalues head (by simp)).1
        exact haccWF
        exact (hvalues head (by simp)).2
      · exact gramAdd_length_v78AggregateFix haccLength
          (hvalues head (by simp)).1
      · exact gramAdd_entries_wf_v78AggregateFix
          accumulator head haccWF (hvalues head (by simp)).2
      · intro value hvalue
        exact hvalues value (by simp [hvalue])

private theorem evalGramV76Fix3_gramSum_v78AggregateFix
    (values : List Gram)
    (hvalues : ∀ value ∈ values,
      value.length = 36 ∧
        ∀ coefficient ∈ value, CoeffWF coefficient) :
    evalGramV76Fix3 (gramSum values) =
      (values.map evalGramV76Fix3).sum := by
  unfold gramSum
  rw [evalGramV76Fix3_foldl_gramAdd_v78AggregateFix
    values gramZero]
  · rw [evalGramV76Fix3_gramZero_v78AggregateFix]
    simp
  · simp [gramZero]
  · exact gramZero_entries_wf_v78AggregateFix
  · exact hvalues

noncomputable def rawFiveGramComplexBridgeV76Fix3_ofFn_v78AggregateFix
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
    exact ⟨gram_ofFn_length_v78AggregateFix (U index) V,
      fun coefficient hcoefficient =>
        gram_entry_wf_v76Fix hcoefficient⟩
  refine
    { traceSquare_eval := ?_
      gramSum_eval := ?_
      gramSum_length := ?_
      gramSum_entry_wf := ?_ }
  · intro index
    exact evalCoeffV71Fix_gramTraceSquare_ofFn_v78TraceFix
      (U index) V
  · change evalGramV76Fix3 (gramSum grams) = _
    rw [evalGramV76Fix3_gramSum_v78AggregateFix grams hgrams]
    simp only [grams, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply]
  · change (gramSum grams).length = 36
    exact (gramSum_invariants_v78AggregateFix grams hgrams).1
  · intro row column
    change CoeffWF
      ((gramSum grams).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero)
    have hinvariants :=
      gramSum_invariants_v78AggregateFix grams hgrams
    apply hinvariants.2
    apply getD_mem_of_lt_v78AggregateFix
    rw [hinvariants.1]
    dsimp only [rawGramFlatIndexV76Fix3]
    omega

theorem rawFiveGramComplexBridgeV76Fix3_ofFn_exists_v78AggregateFix
    (U : Fin 5 → Fin 6 → RawPoint) (V : Fin 6 → RawPoint) :
    RawFiveGramComplexBridgeV76Fix3
      (fun index => List.ofFn (U index)) (List.ofFn V) :=
  rawFiveGramComplexBridgeV76Fix3_ofFn_v78AggregateFix U V

#print axioms rawFiveGramComplexBridgeV76Fix3_ofFn_exists_v78AggregateFix

end
end Fuglede.Z180K30ExceptionalRawV2
