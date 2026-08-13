import Fuglede.Z180K30JointEigenvalueCoreV7
import Fuglede.Z180K30GramJointDataV2

/-! Operator identities transferred to the finite simultaneous eigenbasis. -/

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

structure Z180K30GramOperatorDataV9 where
  core : Z180K30PositiveCommutingGramFamilyV7
  sum_apply :
    forall x, (Fintype.sum fun r => core.family.gram r x) =
      (30 : Complex) • x
  commonProduct : exists Q : Module.End Complex Z180K30JointSpaceV5,
    forall r s, Not (r = s) ->
      (core.family.gram r).comp (core.family.gram s) = Q
  trace_eq :
    forall r, LinearMap.trace Complex Z180K30JointSpaceV5
      (core.family.gram r) = 36

theorem Z180K30GramOperatorDataV9.sum_eigenvalue_eq_thirty
    (data : Z180K30GramOperatorDataV9) (k : Fin 6) :
    (Fintype.sum fun r => data.core.eigenvalue k r) = 30 := by
  have h := data.sum_apply (data.core.family.jointBasis k)
  simp_rw [data.core.gram_apply_jointBasis k] at h
  have hinner := congrArg
    (fun y => inner Complex (data.core.family.jointBasis k) y) h
  have hcomplex :
      (Fintype.sum fun r => (data.core.eigenvalue k r : Complex)) = 30 := by
    simpa using hinner
  exact_mod_cast hcomplex

theorem Z180K30GramOperatorDataV9.common_cross_product
    (data : Z180K30GramOperatorDataV9) (k : Fin 6) :
    exists q : Real, forall r s, Not (r = s) ->
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
  have hcomplex :
      ((data.core.eigenvalue k r * data.core.eigenvalue k s : Real) :
        Complex) =
      inner Complex (data.core.family.jointBasis k)
        (Q (data.core.family.jointBasis k)) := by
    simpa [mul_comm] using hinner
  have hre := congrArg Complex.re hcomplex
  simpa using hre

theorem Z180K30GramOperatorDataV9.sum_eigenvalue_eq_thirtySix
    (data : Z180K30GramOperatorDataV9) (r : Fin 5) :
    (Fintype.sum fun k => data.core.eigenvalue k r) = 36 := by
  have ht := data.trace_eq r
  rw [LinearMap.trace_eq_matrix_trace Complex
    data.core.family.jointBasis.toBasis] at ht
  have hcomplex :
      (Fintype.sum fun k => (data.core.eigenvalue k r : Complex)) = 36 := by
    simpa [Matrix.trace, LinearMap.toMatrix_apply,
      data.core.gram_apply_jointBasis] using ht
  exact_mod_cast hcomplex

noncomputable def Z180K30GramOperatorDataV9.toJointEigenvalueData
    (data : Z180K30GramOperatorDataV9) :
    Z180K30GramJointEigenvalueData where
  eigenvalue := data.core.eigenvalue
  nonnegative := data.core.eigenvalue_nonnegative
  sum_eq_thirty := data.sum_eigenvalue_eq_thirty
  common_cross_product := data.common_cross_product
  trace_eq_thirtySix := data.sum_eigenvalue_eq_thirtySix

theorem Z180K30GramOperatorDataV9.dichotomy
    (data : Z180K30GramOperatorDataV9) :
    (forall k, Z180K30GramNormalScalar (data.core.eigenvalue k)) /
      Z180K30ExceptionalGramEigenvalueData data.core.eigenvalue :=
  data.toJointEigenvalueData.dichotomy

#print axioms Z180K30GramOperatorDataV9.dichotomy

end

end Fuglede
