import Fuglede.Z180K30ExceptionalZetaPowerEvalV76Fix
import Mathlib.Tactic

/-!
# Direct coefficient-zero evaluator for the K30 raw Gram trace

Finite projective leaves only need to know whether coefficient zero is 936.
The evaluator below sums integers directly and never constructs a twelve-entry
coefficient vector.  Its generic correctness theorem ties it to the existing
raw Gram definition.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

/-- Coordinate zero of the reduced thirty-sixth-root power table, evaluated
without constructing a `Coeff`. -/
def zetaScalarZeroV89 (exponent : Nat) : Int :=
  match exponent % 36 with
  | 0 | 30 => 1
  | 12 | 18 => -1
  | _ => 0

def energyScalarZeroV89 (V : RawSet) (difference : Nat) : Int :=
  (V.flatMap fun v =>
    V.map fun w =>
      zetaScalarZeroV89
        (difference * ((v.val + 36 - w.val) % 36))).sum

def gramTraceScalarZeroV89 (U V : RawSet) : Int :=
  (U.flatMap fun u =>
    U.map fun w =>
      energyScalarZeroV89 V
        ((u.val + 36 - w.val) % 36)).sum

theorem zetaScalarZeroV89_eq_getD (exponent : Nat) :
    zetaScalarZeroV89 exponent = (zetaPower exponent).getD 0 0 := by
  unfold zetaScalarZeroV89 zetaPower
  have hlt : exponent % 36 < 36 := Nat.mod_lt _ (by decide)
  interval_cases h : exponent % 36 <;>
    simp [zetaPowerTable, h, coeffZero, List.getD]

private theorem coeffAdd_getD_zero_v89
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    (coeffAdd left right).getD 0 0 =
      left.getD 0 0 + right.getD 0 0 := by
  cases left with
  | nil => simp [CoeffWF] at hleft
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [CoeffWF] at hright
      | cons rightHead rightTail => rfl

private theorem foldl_coeffAdd_getD_zero_v89
    (values : List Coeff) (acc : Coeff)
    (hacc : CoeffWF acc)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    (values.foldl coeffAdd acc).getD 0 0 =
      acc.getD 0 0 + (values.map fun c => c.getD 0 0).sum := by
  induction values generalizing acc with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons]
      rw [ih (acc := coeffAdd acc head)
        (coeffAdd_wf_v71Fix hacc (hvalues head (by simp)))]
      · rw [coeffAdd_getD_zero_v89 hacc (hvalues head (by simp))]
        simp only [List.map_cons, List.sum_cons]
        omega
      · intro c hc
        exact hvalues c (by simp [hc])

private theorem coeffSum_getD_zero_v89
    (values : List Coeff)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    (coeffSum values).getD 0 0 =
      (values.map fun c => c.getD 0 0).sum := by
  unfold coeffSum
  simpa [coeffZero, List.getD] using
    foldl_coeffAdd_getD_zero_v89 values coeffZero
      coeffZero_wf_v71Fix hvalues

private theorem energyScalarZeroV89_eq_getD
    (V : RawSet) (difference : Nat) :
    energyScalarZeroV89 V difference =
      (energy V difference).getD 0 0 := by
  unfold energyScalarZeroV89 energy
  have hsum := coeffSum_getD_zero_v89
    (V.flatMap fun v =>
      V.map fun w =>
        zetaPower (difference * ((v.val + 36 - w.val) % 36)))
    (by
      intro c hc
      rcases List.mem_flatMap.mp hc with ⟨v, _hv, hc⟩
      rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
      exact zetaPower_wf_v76Fix _)
  rw [hsum]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    zetaScalarZeroV89_eq_getD]

theorem gramTraceScalarZeroV89_eq_getD (U V : RawSet) :
    gramTraceScalarZeroV89 U V =
      (gramTraceSquare U V).getD 0 0 := by
  unfold gramTraceScalarZeroV89 gramTraceSquare
  have hsum := coeffSum_getD_zero_v89
    (U.flatMap fun u =>
      U.map fun w => energy V ((u.val + 36 - w.val) % 36))
    (by
      intro c hc
      rcases List.mem_flatMap.mp hc with ⟨u, _hu, hc⟩
      rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
      exact energy_wf_v76Fix V _)
  rw [hsum]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    energyScalarZeroV89_eq_getD]

#print axioms gramTraceScalarZeroV89_eq_getD

end Fuglede.Z180K30ExceptionalRawV2
