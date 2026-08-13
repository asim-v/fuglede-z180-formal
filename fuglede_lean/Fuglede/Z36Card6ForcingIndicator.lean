import Fuglede.Z180K12Projection36Phi6
import Mathlib.Tactic

/-! The exact 36-bit membership indicator of a subset of `ZMod 36`. -/

namespace Fuglede

open Polynomial

def z36MembershipIndicator (A : Finset (ZMod 36)) (i : Fin 36) : Int :=
  if (ZMod.finEquiv 36) i ∈ A then 1 else 0

theorem z36MembershipIndicator_bounds (A : Finset (ZMod 36)) :
    (∀ i, 0 ≤ z36MembershipIndicator A i) ∧
      (∀ i, z36MembershipIndicator A i ≤ 1) := by
  constructor <;> intro i <;>
    unfold z36MembershipIndicator <;> split <;> norm_num

theorem z36MembershipIndicator_sum (A : Finset (ZMod 36)) :
    (∑ i : Fin 36, z36MembershipIndicator A i) = (A.card : Int) := by
  classical
  calc
    (∑ i : Fin 36, z36MembershipIndicator A i) =
        ∑ a : ZMod 36, if a ∈ A then (1 : Int) else 0 := by
      simpa [z36MembershipIndicator] using
        (ZMod.finEquiv 36).sum_comp
          (fun a : ZMod 36 => if a ∈ A then (1 : Int) else 0)
    _ = (A.card : Int) := by simp

theorem projection36IndicatorMask_z36MembershipIndicator
    (A : Finset (ZMod 36)) :
    projection36IndicatorMask (z36MembershipIndicator A) =
      maskPolynomial 36 A := by
  classical
  rw [projection36IndicatorMask, maskPolynomial]
  calc
    (∑ i : Fin 36, monomial i.val (z36MembershipIndicator A i)) =
        ∑ a : ZMod 36,
          if a ∈ A then monomial a.val (1 : Int) else 0 := by
      let g : ZMod 36 → Polynomial Int :=
        fun a => if a ∈ A then monomial a.val (1 : Int) else 0
      calc
        (∑ i : Fin 36, monomial i.val (z36MembershipIndicator A i)) =
            ∑ i : Fin 36, g ((ZMod.finEquiv 36) i) := by
          apply Finset.sum_congr rfl
          intro i _
          unfold z36MembershipIndicator g
          have hval : ((ZMod.finEquiv 36) i).val = i.val := rfl
          by_cases hi : (ZMod.finEquiv 36) i ∈ A
          · simp [hi, hval]
          · simp [hi, hval]
        _ = ∑ a : ZMod 36, g a :=
          (ZMod.finEquiv 36).sum_comp g
        _ = ∑ a : ZMod 36,
            if a ∈ A then monomial a.val (1 : Int) else 0 := rfl
    _ = ∑ a ∈ A, X ^ a.val := by
      simp only [Fintype.sum_ite_mem]
      simp_rw [monomial_one_right_eq_X_pow]

#print axioms z36MembershipIndicator_bounds
#print axioms z36MembershipIndicator_sum
#print axioms projection36IndicatorMask_z36MembershipIndicator

end Fuglede
