import Fuglede.Z180K30JointEigenvalueCoreV7
import Fuglede.Z180K30GramJointDataV2

/-! Operator identities transferred to the finite simultaneous eigenbasis. -/

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

structure Z180K30GramOperatorDataV12 where
  core : Z180K30PositiveCommutingGramFamilyV7
  sum_apply :
    ∀ x, (Finset.univ.sum fun r : Fin 5 => core.family.gram r x) =
      (30 : Complex) • x
  commonProduct : ∃ Q : Module.End Complex Z180K30JointSpaceV5,
    ∀ r s, r ≠ s ->
      (core.family.gram r).comp (core.family.gram s) = Q
  trace_eq :
    ∀ r, LinearMap.trace Complex Z180K30JointSpaceV5
      (core.family.gram r) = 36

theorem Z180K30GramOperatorDataV12.sum_eigenvalue_eq_thirty
    (data : Z180K30GramOperatorDataV12) (k : Fin 6) :
    (Finset.univ.sum fun r : Fin 5 => data.core.eigenvalue k r) = 30 := by
  have h := data.sum_apply (data.core.family.jointBasis k)
  simp_rw [data.core.gram_apply_jointBasis k] at h
  have hinner := congrArg
    (fun y => inner Complex (data.core.family.jointBasis k) y) h
  have hone : inner Complex (data.core.family.jointBasis k)
      (data.core.family.jointBasis k) = 1 := by
    simpa using
      (orthonormal_iff_ite.mp data.core.family.jointBasis.orthonormal k k)
  rw [inner_sum] at hinner
  simp_rw [inner_smul_right, hone, mul_one] at hinner
  exact_mod_cast hinner

theorem Z180K30GramOperatorDataV12.common_cross_product
    (data : Z180K30GramOperatorDataV12) (k : Fin 6) :
    ∃ q : Real, ∀ r s, r ≠ s ->
      data.core.eigenvalue k r * data.core.eigenvalue k s = q := by
  rcases data.commonProduct with ⟨Q, hQ⟩
  refine ⟨Complex.re
      (inner Complex (data.core.family.jointBasis k)
        (Q (data.core.family.jointBasis k))), ?_⟩
  intro r s hrs
  have hop := congrArg
    (fun f : Module.End Complex Z180K30JointSpaceV5 =>
      f (data.core.family.jointBasis k)) (hQ r s hrs)
  simp only [LinearMap.comp_apply] at hop
  rw [data.core.gram_apply_jointBasis k s, map_smul,
    data.core.gram_apply_jointBasis k r, smul_smul] at hop
  have hinner := congrArg
    (fun y => inner Complex (data.core.family.jointBasis k) y) hop
  have hone : inner Complex (data.core.family.jointBasis k)
      (data.core.family.jointBasis k) = 1 := by
    simpa using
      (orthonormal_iff_ite.mp data.core.family.jointBasis.orthonormal k k)
  rw [inner_smul_right, hone, mul_one] at hinner
  have hcomplex :
      ((data.core.eigenvalue k r * data.core.eigenvalue k s : Real) :
        Complex) =
      inner Complex (data.core.family.jointBasis k)
        (Q (data.core.family.jointBasis k)) := by
    simpa [mul_comm] using hinner
  have hre := congrArg Complex.re hcomplex
  simpa using hre

theorem Z180K30GramOperatorDataV12.sum_eigenvalue_eq_thirtySix
    (data : Z180K30GramOperatorDataV12) (r : Fin 5) :
    (Finset.univ.sum fun k : Fin 6 => data.core.eigenvalue k r) = 36 := by
  have ht := data.trace_eq r
  rw [LinearMap.trace_eq_matrix_trace Complex
    data.core.family.jointBasis.toBasis] at ht
  have hdiag (k : Fin 6) :
      (LinearMap.toMatrix data.core.family.jointBasis.toBasis
        data.core.family.jointBasis.toBasis
        (data.core.family.gram r)) k k =
        (data.core.eigenvalue k r : Complex) := by
    rw [LinearMap.toMatrix_apply, data.core.gram_apply_jointBasis]
    rw [map_smul]
    simp
  rw [Matrix.trace] at ht
  simp_rw [hdiag] at ht
  exact_mod_cast ht

noncomputable def Z180K30GramOperatorDataV12.toJointEigenvalueData
    (data : Z180K30GramOperatorDataV12) :
    Z180K30GramJointEigenvalueData where
  eigenvalue := data.core.eigenvalue
  nonnegative := data.core.eigenvalue_nonnegative
  sum_eq_thirty := data.sum_eigenvalue_eq_thirty
  common_cross_product := data.common_cross_product
  trace_eq_thirtySix := data.sum_eigenvalue_eq_thirtySix

theorem Z180K30GramOperatorDataV12.dichotomy
    (data : Z180K30GramOperatorDataV12) :
    (∀ k, Z180K30GramNormalScalar (data.core.eigenvalue k)) ∨
      Z180K30ExceptionalGramEigenvalueData data.core.eigenvalue :=
  data.toJointEigenvalueData.dichotomy

#print axioms Z180K30GramOperatorDataV12.dichotomy

end

end Fuglede
