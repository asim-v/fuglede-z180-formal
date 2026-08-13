import Fuglede.Z180K30ExceptionalZetaPowerEvalV76Fix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! # Complex reflection of the raw K30 Gram certificate (V76 Fix3) -/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators
noncomputable section

abbrev RawComplexGramV76Fix3 := Matrix (Fin 6) (Fin 6) Complex

def rawGramFlatIndexV76Fix3 (row column : Fin 6) : Nat :=
  row.val * 6 + column.val

noncomputable def evalGramV76Fix3 (entries : Gram) : RawComplexGramV76Fix3 :=
  fun row column =>
    evalCoeffV71Fix
      (entries.getD (rawGramFlatIndexV76Fix3 row column) coeffZero)

@[simp]
theorem gramTarget30_length_v76Fix3 : gramTarget30.length = 36 := by
  simp [gramTarget30]

theorem gramTarget30_getD_wf_v76Fix3 (row column : Fin 6) :
    CoeffWF
      (gramTarget30.getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero) := by
  fin_cases row <;> fin_cases column <;>
    simp [CoeffWF, rawGramFlatIndexV76Fix3, gramTarget30,
      coeffZero, scalarCoeff]

theorem evalGramV76Fix3_gramTarget30 :
    evalGramV76Fix3 gramTarget30 =
      (30 : Complex) • (1 : RawComplexGramV76Fix3) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [evalGramV76Fix3, rawGramFlatIndexV76Fix3, gramTarget30,
      evalCoeffV71Fix_coeffZero_v71Fix3,
      evalCoeffV71Fix_scalarCoeff_v71Fix3]

structure RawFiveGramComplexBridgeV76Fix3
    (U : Fin 5 → RawSet) (V : RawSet) where
  traceSquare_eval : ∀ r : Fin 5,
    evalCoeffV71Fix (gramTraceSquare (U r) V) =
      Matrix.trace
        (evalGramV76Fix3 (gram (U r) V) *
          evalGramV76Fix3 (gram (U r) V))
  gramSum_eval :
    evalGramV76Fix3
        (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
      ∑ r : Fin 5, evalGramV76Fix3 (gram (U r) V)
  gramSum_length :
    (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)).length = 36
  gramSum_entry_wf : ∀ row column : Fin 6,
    CoeffWF
      ((gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)).getD
        (rawGramFlatIndexV76Fix3 row column) coeffZero)

private theorem list_eq_of_getD_eq_v76Fix3
    {alpha : Type*} (fallback : alpha)
    {left right : List alpha}
    (hlen : left.length = right.length)
    (hgetD : ∀ n, n < left.length →
      left.getD n fallback = right.getD n fallback) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons b right => simp at hlen
  | cons a left ih =>
      cases right with
      | nil => simp at hlen
      | cons b right =>
          have hab : a = b := by
            have hzero := hgetD 0 (by simp)
            change a = b at hzero
            exact hzero
          have hlenTail : left.length = right.length := by
            simpa using hlen
          have hgetDTail : ∀ n, n < left.length →
              left.getD n fallback = right.getD n fallback := by
            intro n hn
            have hsucc := hgetD (Nat.succ n) (by
              simpa using Nat.succ_lt_succ hn)
            change left.getD n fallback = right.getD n fallback at hsucc
            exact hsucc
          subst b
          exact congrArg (List.cons a) (ih hlenTail hgetDTail)

theorem fiveGramStarB_of_complex_certificate_v76Fix3
    (U : Fin 5 → RawSet) (V : RawSet)
    (bridge : RawFiveGramComplexBridgeV76Fix3 U V)
    (hvalidU : ∀ r : Fin 5, validSixSetB (U r) = true)
    (hvalidV : validSixSetB V = true)
    (hcover : ∀ r : Fin 5, rankTwoProjectiveCoverB (U r) V = true)
    (htrace : ∀ r : Fin 5,
      Matrix.trace
        (evalGramV76Fix3 (gram (U r) V) *
          evalGramV76Fix3 (gram (U r) V)) = (936 : Complex))
    (hsum :
      (∑ r : Fin 5, evalGramV76Fix3 (gram (U r) V)) =
        (30 : Complex) • (1 : RawComplexGramV76Fix3)) :
    fiveGramStarB U V = true := by
  have htraceRaw : ∀ r : Fin 5,
      gramTraceSquare (U r) V = scalarCoeff 936 := by
    intro r
    apply evalCoeffV71Fix_injective_of_wf_v71Fix3
      (gramTraceSquare_wf_v76Fix (U r) V)
      (scalarCoeff_wf_v71Fix 936)
    calc
      evalCoeffV71Fix (gramTraceSquare (U r) V) =
          Matrix.trace
            (evalGramV76Fix3 (gram (U r) V) *
              evalGramV76Fix3 (gram (U r) V)) :=
        bridge.traceSquare_eval r
      _ = (936 : Complex) := htrace r
      _ = evalCoeffV71Fix (scalarCoeff 936) := by
        symm
        exact evalCoeffV71Fix_scalarCoeff_v71Fix3 936
  have hsumEvaluated :
      evalGramV76Fix3
          (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
        evalGramV76Fix3 gramTarget30 := by
    calc
      evalGramV76Fix3
          (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
          ∑ r : Fin 5, evalGramV76Fix3 (gram (U r) V) :=
        bridge.gramSum_eval
      _ = (30 : Complex) • (1 : RawComplexGramV76Fix3) := hsum
      _ = evalGramV76Fix3 gramTarget30 :=
        evalGramV76Fix3_gramTarget30.symm
  have hsumRaw :
      gramSum (List.ofFn fun r : Fin 5 => gram (U r) V) =
        gramTarget30 := by
    apply list_eq_of_getD_eq_v76Fix3 coeffZero
    · exact bridge.gramSum_length.trans gramTarget30_length_v76Fix3.symm
    · intro n hn
      have hn36 : n < 36 := by
        rw [bridge.gramSum_length] at hn
        exact hn
      let row : Fin 6 := ⟨n / 6, by omega⟩
      let column : Fin 6 := ⟨n % 6, Nat.mod_lt n (by norm_num)⟩
      have hindex : rawGramFlatIndexV76Fix3 row column = n := by
        dsimp [rawGramFlatIndexV76Fix3, row, column]
        simpa [Nat.mul_comm] using Nat.div_add_mod n 6
      apply evalCoeffV71Fix_injective_of_wf_v71Fix3
        (by simpa [hindex] using bridge.gramSum_entry_wf row column)
        (by simpa [hindex] using
          gramTarget30_getD_wf_v76Fix3 row column)
      have hentry := congrFun (congrFun hsumEvaluated row) column
      simpa [evalGramV76Fix3, hindex] using hentry
  have hexceptional : ∀ r : Fin 5,
      exceptionalPairB (U r) V = true := by
    intro r
    simp [exceptionalPairB, hvalidU r, hvalidV, hcover r, htraceRaw r]
  have hall :
      (List.ofFn fun r : Fin 5 => exceptionalPairB (U r) V).all id = true := by
    rw [List.all_eq_true]
    intro flag hflag
    rcases List.mem_ofFn.mp hflag with ⟨r, rfl⟩
    exact hexceptional r
  unfold fiveGramStarB
  rw [hall, hsumRaw]
  simp

#print axioms evalGramV76Fix3_gramTarget30
#print axioms fiveGramStarB_of_complex_certificate_v76Fix3

end
end Fuglede.Z180K30ExceptionalRawV2
