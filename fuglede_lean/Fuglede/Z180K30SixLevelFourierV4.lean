import Fuglede.Z180K30SixLevelCoreV4

/-!
# Fourier summation for the six mixed-radix levels
-/

namespace Fuglede

open scoped BigOperators ZMod

theorem fourierSum_add_kernel30Lift_eq_dft
    (X : Finset (ZMod 180)) (u : ZMod 180) (b : ZMod 6) :
    fourierSum X (u + z180K30Kernel30Lift (-b)) =
      ZMod.dft (z180K30SixLevelFourierSum X u) b := by
  classical
  let coord : ZMod 180 → ZMod 6 := z180K30Projection6
  let weight : ZMod 180 → ℂ := fun x ↦
    ZMod.stdAddChar (x * u) * ZMod.stdAddChar (-(coord x * b))
  have hfiber :
      (∑ c : ZMod 6, ∑ x ∈ X.filter (fun x ↦ coord x = c), weight x) =
        ∑ x ∈ X, weight x := by
    simpa using Finset.sum_fiberwise X coord weight
  calc
    fourierSum X (u + z180K30Kernel30Lift (-b)) =
        ∑ x ∈ X, weight x := by
      rw [fourierSum_eq_finset_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [weight, coord]
      rw [mul_add, AddChar.map_add_eq_mul,
        z180_stdAddChar_mul_kernel30Lift_eq]
      congr 2
      ring
    _ = ∑ c : ZMod 6,
        ∑ x ∈ X.filter (fun x ↦ coord x = c), weight x := hfiber.symm
    _ = ∑ c : ZMod 6,
        ZMod.stdAddChar (-(c * b)) * z180K30SixLevelFourierSum X u c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [z180K30SixLevelFourierSum, z180K30SixthSlice,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hcoord : coord x = c := (Finset.mem_filter.mp hx).2
      simp only [weight]
      rw [hcoord, mul_comm]
    _ = ZMod.dft (z180K30SixLevelFourierSum X u) b := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]

theorem sum_z180K30SixLevelFourierSum_eq
    (X : Finset (ZMod 180)) (u : ZMod 180) :
    (∑ c : ZMod 6, z180K30SixLevelFourierSum X u c) = fourierSum X u := by
  have h := fourierSum_add_kernel30Lift_eq_dft X u 0
  rw [neg_zero, z180K30Kernel30Lift_zero, add_zero,
    ZMod.dft_apply_zero] at h
  exact h.symm

theorem z180K30SixLevelFourierSum_eq_zero_of_all_lifts
    (X : Finset (ZMod 180)) (u : ZMod 180)
    (hzero : ∀ b : ZMod 6,
      fourierSum X (u + z180K30Kernel30Lift (-b)) = 0) :
    ∀ c : ZMod 6, z180K30SixLevelFourierSum X u c = 0 := by
  have heq : ∀ c c' : ZMod 6,
      z180K30SixLevelFourierSum X u c =
        z180K30SixLevelFourierSum X u c' := by
    apply eq_of_dft_eq_zero_off_zero
    intro b hb
    rw [← fourierSum_add_kernel30Lift_eq_dft]
    exact hzero b
  have hsumzero :
      (∑ c : ZMod 6, z180K30SixLevelFourierSum X u c) = 0 := by
    rw [sum_z180K30SixLevelFourierSum_eq]
    simpa using hzero 0
  intro c
  have hsix :
      (6 : ℂ) * z180K30SixLevelFourierSum X u c = 0 := by
    rw [← hsumzero]
    simp_rw [heq _ c]
    norm_num
  exact (mul_eq_zero.mp hsix).resolve_left (by norm_num)

theorem z180K30SixLevelFourierSum_eq_phase_mul_fourierSum
    (X : Finset (ZMod 180)) (u : ZMod 180) (c : ZMod 6) :
    z180K30SixLevelFourierSum X u c =
      ZMod.stdAddChar ((c.val : ZMod 180) * u) *
        fourierSum (z180K30SixthFibre X c) (z180K30Projection30 u) := by
  classical
  let S := z180K30SixthSlice X c
  have hinj : Set.InjOn z180K30SixthDigit (S : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply z180K30SixthDigit_injective_on_sixth_slice c
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy
  calc
    z180K30SixLevelFourierSum X u c =
        ∑ x ∈ S, ZMod.stdAddChar (x * u) := rfl
    _ = ∑ x ∈ S,
        ZMod.stdAddChar ((c.val : ZMod 180) * u) *
          ZMod.stdAddChar
            (z180K30SixthDigit x * z180K30Projection30 u) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hc : z180K30Projection6 x = c := (Finset.mem_filter.mp hx).2
      rw [← hc]
      exact z180_stdAddChar_eq_sixthDigit_factor x u
    _ = ZMod.stdAddChar ((c.val : ZMod 180) * u) *
        (∑ x ∈ S,
          ZMod.stdAddChar
            (z180K30SixthDigit x * z180K30Projection30 u)) := by
      rw [Finset.mul_sum]
    _ = ZMod.stdAddChar ((c.val : ZMod 180) * u) *
        (∑ q ∈ z180K30SixthFibre X c,
          ZMod.stdAddChar (q * z180K30Projection30 u)) := by
      dsimp only [S, z180K30SixthFibre, z180K30SixthSlice] at hinj ⊢
      rw [Finset.sum_image hinj]
    _ = ZMod.stdAddChar ((c.val : ZMod 180) * u) *
        fourierSum (z180K30SixthFibre X c)
          (z180K30Projection30 u) := by
      rw [fourierSum_eq_finset_sum]

#print axioms fourierSum_add_kernel30Lift_eq_dft
#print axioms z180K30SixLevelFourierSum_eq_zero_of_all_lifts
#print axioms z180K30SixLevelFourierSum_eq_phase_mul_fourierSum

end Fuglede
