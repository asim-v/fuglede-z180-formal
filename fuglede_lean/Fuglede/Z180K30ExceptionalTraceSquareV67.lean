import Fuglede.Z180K30ExceptionalSpectrumV62
import Mathlib.Tactic

/-!
# Trace-square identity in the exceptional K30 Gram branch

The exceptional joint spectrum on each row is exactly `30, 6, 0, 0, 0, 0`.
This module records both its scalar square sum and the corresponding operator
trace identity.
-/

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

theorem Z180K30ExceptionalGramEigenvalueData.sum_sq_eq_936_v67
    {lambda : Fin 6 → Fin 5 → ℝ}
    (hex : Z180K30ExceptionalGramEigenvalueData lambda) (r : Fin 5) :
    (∑ k : Fin 6, (lambda k r) ^ 2) = 936 := by
  classical
  obtain ⟨k6, k30, hkne, hk6, hk30, hzero⟩ :=
    hex.exists_row_normal_spike_zero_v62 r
  have hk6val : lambda k6 r = 6 := hk6 r
  have hk30val : lambda k30 r = 30 := hk30.1
  calc
    (∑ k : Fin 6, (lambda k r) ^ 2) =
        ∑ k : Fin 6,
          ((if k = k6 then (36 : ℝ) else 0) +
           (if k = k30 then (900 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases h6 : k = k6
      · subst k
        norm_num [hk6val, hkne]
      · by_cases h30 : k = k30
        · subst k
          norm_num [hk30val, hkne.symm]
        · rw [hzero k h6 h30]
          simp [h6, h30]
    _ = 936 := by
      rw [Finset.sum_add_distrib]
      simp

theorem z180_k30_joint_square_coordinate_v67
    (core : Z180K30PositiveCommutingGramFamilyV7)
    (r : Fin 5) (k : Fin 6) :
    (LinearMap.toMatrix core.family.jointBasis.toBasis
      core.family.jointBasis.toBasis
      ((core.family.gram r).comp (core.family.gram r))) k k =
      ((core.eigenvalue k r : Complex) ^ 2) := by
  rw [LinearMap.toMatrix_apply]
  change
    (core.family.jointBasis.toBasis.repr
      (((core.family.gram r).comp (core.family.gram r))
        (core.family.jointBasis k))) k =
      ((core.eigenvalue k r : Complex) ^ 2)
  rw [LinearMap.comp_apply]
  rw [core.gram_apply_jointBasis]
  rw [map_smul]
  rw [core.gram_apply_jointBasis]
  rw [smul_smul]
  rw [core.family.jointBasis.coe_toBasis_repr_apply]
  rw [core.family.jointBasis.repr_apply_apply]
  rw [inner_smul_right, core.family.jointBasis.inner_eq_one, mul_one]
  rw [pow_two]

theorem z180_k30_joint_trace_square_v67
    (core : Z180K30PositiveCommutingGramFamilyV7) (r : Fin 5) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      ((core.family.gram r).comp (core.family.gram r)) =
      (∑ k : Fin 6, ((core.eigenvalue k r : Complex) ^ 2)) := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    core.family.jointBasis.toBasis]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro k _hk
  exact z180_k30_joint_square_coordinate_v67 core r k

theorem z180_k30_exceptional_trace_square_eq_936_v67
    (core : Z180K30PositiveCommutingGramFamilyV7)
    (hex : Z180K30ExceptionalGramEigenvalueData core.eigenvalue)
    (r : Fin 5) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      ((core.family.gram r).comp (core.family.gram r)) = 936 := by
  rw [z180_k30_joint_trace_square_v67]
  exact_mod_cast hex.sum_sq_eq_936_v67 r

#print axioms Z180K30ExceptionalGramEigenvalueData.sum_sq_eq_936_v67
#print axioms z180_k30_exceptional_trace_square_eq_936_v67

end
end Fuglede
