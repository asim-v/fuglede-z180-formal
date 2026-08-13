import Fuglede.FourierTiling
import Fuglede.ZModDFTSupport
import Fuglede.Z30K5InflationBridge
import Fuglede.Z180K30ExceptionalBoundary
import Mathlib.Tactic

/-!
# Six-level Fourier descent for the exceptional `ZMod 180`, `k = 30` branch

Reduction modulo six partitions a set into six mixed-radix slices.  Writing
`x.val = c + 6 q` identifies each slice with a subset of `ZMod 30`.
Changing a frequency by a multiple of thirty is exactly the `ZMod 6` DFT of
the six slice sums.  This is the bookkeeping needed by the concrete H-coset
exceptional bridge.
-/

namespace Fuglede

open scoped BigOperators ZMod

/-- Reduction modulo six. -/
def z180K30Projection6 : ZMod 180 →+ ZMod 6 :=
  (ZMod.castHom (by norm_num : 6 ∣ 180) (ZMod 6)).toAddMonoidHom

@[simp]
theorem z180K30Projection6_apply (x : ZMod 180) :
    z180K30Projection6 x = ZMod.cast x := rfl

/-- The kernel of reduction modulo thirty, parametrized by `ZMod 6`. -/
def z180K30Kernel30Lift (b : ZMod 6) : ZMod 180 :=
  (30 * b.val : Nat)

/-- The quotient digit in the mixed-radix expansion `x.val = c + 6 q`. -/
def z180K30SixthDigit (x : ZMod 180) : ZMod 30 :=
  (x.val / 6 : Nat)

/-- One residue-six slice, represented by its quotient digits in `ZMod 30`. -/
noncomputable def z180K30SixthFibre
    (X : Finset (ZMod 180)) (c : ZMod 6) : Finset (ZMod 30) :=
  (X.filter fun x ↦ z180K30Projection6 x = c).image z180K30SixthDigit

/-- Unprojected residue-six slice. -/
noncomputable def z180K30SixthSlice
    (X : Finset (ZMod 180)) (c : ZMod 6) : Finset (ZMod 180) :=
  X.filter fun x ↦ z180K30Projection6 x = c

/-- The contribution of one residue-six slice at a fixed base frequency. -/
noncomputable def z180K30SixLevelFourierSum
    (X : Finset (ZMod 180)) (u : ZMod 180) (c : ZMod 6) : ℂ :=
  ∑ x ∈ z180K30SixthSlice X c, ZMod.stdAddChar (x * u)

theorem z180K30Kernel30Lift_injective :
    Function.Injective z180K30Kernel30Lift := by
  decide

@[simp]
theorem z180K30Kernel30Lift_zero :
    z180K30Kernel30Lift 0 = 0 := by
  decide

@[simp]
theorem z180K30Projection30_kernel30Lift (b : ZMod 6) :
    z180K30Projection30 (z180K30Kernel30Lift b) = 0 := by
  revert b
  decide

/-- Exact mixed-radix reconstruction. -/
theorem z180K30_sixthDigit_reconstruction :
    ∀ x : ZMod 180,
      ((z180K30Projection6 x).val : ZMod 180) +
        z30K5ScaleSix180 (z180K30SixthDigit x) = x := by
  intro x
  fin_cases x <;> decide

/-- The quotient digit is injective after fixing the residue modulo six. -/
theorem z180K30SixthDigit_injective_on_sixth_slice :
    ∀ c : ZMod 6,
      Set.InjOn z180K30SixthDigit
        {x : ZMod 180 | z180K30Projection6 x = c} := by
  intro c x hx y hy hdigit
  rw [← z180K30_sixthDigit_reconstruction x,
    ← z180K30_sixthDigit_reconstruction y, hx, hy, hdigit]

/-- In one residue-six slice, equality modulo thirty is exactly equality of
the quotient digits modulo five. -/
theorem z180K30_projection30_eq_iff_sixthDigit_cast5_eq :
    ∀ x y : ZMod 180,
      z180K30Projection6 x = z180K30Projection6 y →
      (z180K30Projection30 x = z180K30Projection30 y ↔
        (ZMod.cast (z180K30SixthDigit x) : ZMod 5) =
          ZMod.cast (z180K30SixthDigit y)) := by
  intro x
  fin_cases x <;> decide

/-- A kernel-thirty frequency restricts to the standard character on the
residue-six coordinate. -/
theorem z180_stdAddChar_mul_kernel30Lift_eq
    (x : ZMod 180) (b : ZMod 6) :
    ZMod.stdAddChar (x * z180K30Kernel30Lift b) =
      ZMod.stdAddChar (z180K30Projection6 x * b) := by
  calc
    ZMod.stdAddChar (x * z180K30Kernel30Lift b) =
        ZMod.stdAddChar
          ((x.val : ZMod 180) * ((30 * b.val : Nat) : ZMod 180)) := by
      rw [ZMod.natCast_zmod_val]
      rfl
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (30 * (b.val : ℤ)) : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (30 * (b.val : ℤ)) : ℤ) : ℂ) /
            (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (b.val : ℤ) : ℤ) : ℂ) / (6 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod 6)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar (z180K30Projection6 x * b) := by
      congr 1
      push_cast
      rw [z180K30Projection6_apply, ZMod.cast_eq_val,
        ZMod.natCast_zmod_val]

/-- The scale-six point embedding is dual to reduction of the frequency
modulo thirty. -/
theorem z180_stdAddChar_scaleSix_mul_eq
    (q : ZMod 30) (u : ZMod 180) :
    ZMod.stdAddChar (z30K5ScaleSix180 q * u) =
      ZMod.stdAddChar (q * z180K30Projection30 u) := by
  calc
    ZMod.stdAddChar (z30K5ScaleSix180 q * u) =
        ZMod.stdAddChar
          ((((6 * (q.val : ℤ)) * (u.val : ℤ) : ℤ) : ZMod 180)) := by
      congr 1
      change (((6 * q.val : Nat) : ZMod 180) * u) =
        (6 : ZMod 180) * (q.val : ZMod 180) * (u.val : ZMod 180)
      push_cast
      rw [ZMod.natCast_zmod_val]
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          ((((6 * (q.val : ℤ)) * (u.val : ℤ) : ℤ) : ℤ) : ℂ) /
            (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          ((((q.val : ℤ) * (u.val : ℤ) : ℤ) : ℤ) : ℂ) /
            (30 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((q.val : ℤ) * (u.val : ℤ) : ℤ) : ZMod 30)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar (q * z180K30Projection30 u) := by
      congr 1
      change (q.val : ZMod 30) * (u.val : ZMod 30) =
        q * (u.val : ZMod 30)
      rw [ZMod.natCast_zmod_val]

/-- Mixed-radix factorization of one character value. -/
theorem z180_stdAddChar_eq_sixthDigit_factor
    (x u : ZMod 180) :
    ZMod.stdAddChar (x * u) =
      ZMod.stdAddChar (((z180K30Projection6 x).val : ZMod 180) * u) *
        ZMod.stdAddChar
          (z180K30SixthDigit x * z180K30Projection30 u) := by
  conv_lhs =>
    rw [← z180K30_sixthDigit_reconstruction x]
  rw [add_mul, AddChar.map_add_eq_mul,
    z180_stdAddChar_scaleSix_mul_eq]

/-- Varying a frequency through its six lifts modulo thirty is exactly the
DFT of the six residue-level sums. -/
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

/-- The sum of the six level contributions is the base Fourier sum. -/
theorem sum_z180K30SixLevelFourierSum_eq
    (X : Finset (ZMod 180)) (u : ZMod 180) :
    (∑ c : ZMod 6, z180K30SixLevelFourierSum X u c) = fourierSum X u := by
  have h := fourierSum_add_kernel30Lift_eq_dft X u 0
  rw [neg_zero, z180K30Kernel30Lift_zero, add_zero,
    ZMod.dft_apply_zero] at h
  exact h.symm

/-- If all six frequency lifts vanish, every residue-level sum vanishes. -/
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

/-- One six-level sum is a nonzero phase times the Fourier sum of the mixed-
radix quotient fibre in `ZMod 30`. -/
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

