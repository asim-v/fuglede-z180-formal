import Fuglede.Z180K30ExceptionalZetaPowerEvalV76
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Complex reflection of the raw K30 Gram certificate

Raw Gram matrices are stored as row-major lists of thirty-six integral
coefficient vectors.  This module evaluates such a list entrywise at the
standard primitive thirty-sixth root and packages the two exact identities
needed from the analytic side:

* `gramTraceSquare` evaluates to `trace (G * G)` for every one of the five
  column Gram matrices;
* evaluating `gramSum` agrees with the sum of those five matrices.

Once those identities are supplied, `trace (G * G) = 936` and
`sum G = 30 I` reflect through the injective twelve-coordinate evaluator and
produce `fiveGramStarB = true`.  Thus later modules constructing the bridge
from the actual dephased Fourier blocks have a small, explicit interface.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open scoped BigOperators

noncomputable section

/-- The complex six-by-six matrix represented by a raw Gram list. -/
abbrev RawComplexGramV76 := Matrix (Fin 6) (Fin 6) Complex

/-- Row-major position of a six-by-six matrix entry. -/
def rawGramFlatIndexV76 (row column : Fin 6) : Nat :=
  row.val * 6 + column.val

/-- Entrywise evaluation of a raw Gram list at `zeta36V71Fix`. -/
noncomputable def evalGramV76 (entries : Gram) : RawComplexGramV76 :=
  fun row column =>
    evalCoeffV71Fix
      (entries.getD (rawGramFlatIndexV76 row column) coeffZero)

@[simp]
theorem gramTarget30_length_v76 : gramTarget30.length = 36 := by
  simp [gramTarget30]

theorem gramTarget30_getD_wf_v76 (row column : Fin 6) :
    CoeffWF
      (gramTarget30.getD (rawGramFlatIndexV76 row column) coeffZero) := by
  fin_cases row <;> fin_cases column <;>
    simp [rawGramFlatIndexV76, gramTarget30,
      coeffZero_wf_v71Fix, scalarCoeff_wf_v71Fix]

/-- The raw target evaluates to the scalar matrix `30 I`. -/
theorem evalGramV76_gramTarget30 :
    evalGramV76 gramTarget30 =
      (30 : Complex) • (1 : RawComplexGramV76) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [evalGramV76, rawGramFlatIndexV76, gramTarget30,
      evalCoeffV71Fix_coeffZero_v71Fix3,
      evalCoeffV71Fix_scalarCoeff_v71Fix3]

/--
The exact interface between a five-family of raw Gram lists and its complex
matrices.  The well-formedness field is deliberately local to the aggregate
list: it is precisely what injectivity needs and avoids coupling this module
to a particular construction of the five fibres.
-/
structure RawFiveGramComplexBridgeV76
    (U : Fin 5 → RawSet) (V : RawSet) where
  traceSquare_eval : ∀ r : Fin 5,
    evalCoeffV71Fix (gramTraceSquare (U r) V) =
      Matrix.trace
        (evalGramV76 (gram (U r) V) *
          evalGramV76 (gram (U r) V))
  gramSum_eval :
    evalGramV76
        (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
      ∑ r : Fin 5, evalGramV76 (gram (U r) V)
  gramSum_length :
    (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)).length = 36
  gramSum_entry_wf : ∀ row column : Fin 6,
    CoeffWF
      ((gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)).getD
        (rawGramFlatIndexV76 row column) coeffZero)

private theorem list_eq_of_getD_eq_v76
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

/--
Reflection theorem for the complete raw five-Gram predicate.  No numerical
approximation is involved: equality in `Complex` is sent back to equality of
the twelve integral coordinates by V71 Fix3.
-/
theorem fiveGramStarB_of_complex_certificate_v76
    (U : Fin 5 → RawSet) (V : RawSet)
    (bridge : RawFiveGramComplexBridgeV76 U V)
    (hvalidU : ∀ r : Fin 5, validSixSetB (U r) = true)
    (hvalidV : validSixSetB V = true)
    (hcover : ∀ r : Fin 5, rankTwoProjectiveCoverB (U r) V = true)
    (htrace : ∀ r : Fin 5,
      Matrix.trace
        (evalGramV76 (gram (U r) V) *
          evalGramV76 (gram (U r) V)) = (936 : Complex))
    (hsum :
      (∑ r : Fin 5, evalGramV76 (gram (U r) V)) =
        (30 : Complex) • (1 : RawComplexGramV76)) :
    fiveGramStarB U V = true := by
  have htraceRaw : ∀ r : Fin 5,
      gramTraceSquare (U r) V = scalarCoeff 936 := by
    intro r
    apply evalCoeffV71Fix_injective_of_wf_v71Fix3
      (gramTraceSquare_wf_v76 (U r) V)
      (scalarCoeff_wf_v71Fix 936)
    calc
      evalCoeffV71Fix (gramTraceSquare (U r) V) =
          Matrix.trace
            (evalGramV76 (gram (U r) V) *
              evalGramV76 (gram (U r) V)) :=
        bridge.traceSquare_eval r
      _ = (936 : Complex) := htrace r
      _ = evalCoeffV71Fix (scalarCoeff 936) := by
        symm
        exact evalCoeffV71Fix_scalarCoeff_v71Fix3 936
  have hsumEvaluated :
      evalGramV76
          (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
        evalGramV76 gramTarget30 := by
    calc
      evalGramV76
          (gramSum (List.ofFn fun r : Fin 5 => gram (U r) V)) =
          ∑ r : Fin 5, evalGramV76 (gram (U r) V) :=
        bridge.gramSum_eval
      _ = (30 : Complex) • (1 : RawComplexGramV76) := hsum
      _ = evalGramV76 gramTarget30 := evalGramV76_gramTarget30.symm
  have hsumRaw :
      gramSum (List.ofFn fun r : Fin 5 => gram (U r) V) =
        gramTarget30 := by
    apply list_eq_of_getD_eq_v76 coeffZero
    · exact bridge.gramSum_length.trans gramTarget30_length_v76.symm
    · intro n hn
      have hn36 : n < 36 := by
        simpa [bridge.gramSum_length] using hn
      let row : Fin 6 := ⟨n / 6, by omega⟩
      let column : Fin 6 := ⟨n % 6, Nat.mod_lt n (by norm_num)⟩
      have hindex : rawGramFlatIndexV76 row column = n := by
        dsimp [rawGramFlatIndexV76, row, column]
        omega
      apply evalCoeffV71Fix_injective_of_wf_v71Fix3
        (by simpa [hindex] using bridge.gramSum_entry_wf row column)
        (by simpa [hindex] using gramTarget30_getD_wf_v76 row column)
      have hentry := congrFun (congrFun hsumEvaluated row) column
      simpa [evalGramV76, hindex] using hentry
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

#print axioms evalGramV76_gramTarget30
#print axioms fiveGramStarB_of_complex_certificate_v76

end
end Fuglede.Z180K30ExceptionalRawV2
