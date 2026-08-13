import Fuglede.Z180FiveLevelFourier
import Fuglede.Z180K30Fibres
import Mathlib.Tactic

/-!
# Fourier identification for a fifth-coordinate fibre

The dual embedding `ZMod 36 → ZMod 180` is multiplication by five.  At such
a lifted frequency the global character restricts to the standard character
on the projected `ZMod 36` fibre.  This file records the exact finite-sum
identity needed by the `k = 30` common-spectrum bridge.
-/

namespace Fuglede

/-- The quotient map, as an additive homomorphism for Fourier calculations. -/
def z180K30Projection36 : ZMod 180 →+ ZMod 36 :=
  (ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod 36)).toAddMonoidHom

@[simp]
theorem z180K30Projection36_apply (x : ZMod 180) :
    z180K30Projection36 x = ZMod.cast x := rfl

/-- Raw fifth-coordinate slice before its injective projection to `ZMod 36`. -/
noncomputable def z180K30FifthSlice
    (X : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 180) :=
  X.filter fun x ↦ (ZMod.cast x : ZMod 5) = c

/-- Dual lift of a `ZMod 36` frequency to a frequency of `ZMod 180`. -/
def z180K30LiftFrequency36 (d : ZMod 36) : ZMod 180 :=
  (5 * d.val : ℕ)

/-- The lifted frequency has zero fifth CRT coordinate. -/
theorem z180K30LiftFrequency36_fifthCoord (d : ZMod 36) :
    crt180FifthCoord (toCRT180 (z180K30LiftFrequency36 d)) = 0 := by
  rw [crt180FifthCoord_toCRT180]
  unfold z180K30LiftFrequency36
  push_cast
  rw [ZMod.cast_mul (by norm_num : 5 ∣ 180)]
  have h5 : (ZMod.cast (5 : ZMod 180) : ZMod 5) = 0 := by decide
  rw [h5, zero_mul]

/-- The dual lift preserves exact additive order. -/
theorem frequencyOrder_z180K30LiftFrequency36 (d : ZMod 36) :
    frequencyOrder 180 (z180K30LiftFrequency36 d) =
      frequencyOrder 36 d := by
  revert d
  decide

/-- A difference with zero fifth coordinate has the same order as its
projection to `ZMod 36`. -/
theorem z180_frequencyOrder_eq_projection36_of_fifthCoordinate_zero
    (d : ZMod 180) (hfive : (ZMod.cast d : ZMod 5) = 0) :
    frequencyOrder 180 d = frequencyOrder 36 (z180K30Projection36 d) := by
  have hnatCastZero : (d.val : ZMod 5) = 0 := by
    simpa only [ZMod.cast_eq_val] using hfive
  have hdvd : 5 ∣ d.val :=
    (ZMod.natCast_eq_zero_iff d.val 5).mp hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hklt : k < 36 := by
    have hlt := d.val_lt
    omega
  unfold frequencyOrder
  rw [z180K30Projection36_apply, ZMod.cast_eq_val,
    ZMod.val_natCast]
  rw [hk]
  interval_cases k <;> norm_num

/-- Multiplication by a lifted frequency carries exactly the character of
the projected point-frequency product in `ZMod 36`. -/
theorem z180_stdAddChar_mul_liftFrequency36_eq
    (x : ZMod 180) (d : ZMod 36) :
    ZMod.stdAddChar (x * z180K30LiftFrequency36 d) =
      ZMod.stdAddChar ((z180K30Projection36 x) * d) := by
  calc
    ZMod.stdAddChar (x * z180K30LiftFrequency36 d) =
        ZMod.stdAddChar
          ((x.val : ZMod 180) * ((5 * d.val : ℕ) : ZMod 180)) := by
      rw [ZMod.natCast_zmod_val]
      rfl
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (5 * (d.val : ℤ)) : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (5 * (d.val : ℤ)) : ℤ) : ℂ) / (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (d.val : ℤ) : ℤ) : ℂ) / (36 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (d.val : ℤ) : ℤ) : ZMod 36)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar ((z180K30Projection36 x) * d) := by
      congr 1
      push_cast
      rw [z180K30Projection36_apply, ZMod.cast_eq_val,
        ZMod.natCast_zmod_val]

/-- The Fourier sum of a projected fibre is one five-level Fourier sum of
the original set at the dual lifted frequency. -/
theorem fourierSum_z180K30FifthFiber36
    (X : Finset (ZMod 180)) (c : ZMod 5)
    (d : ZMod 36) :
    fourierSum (z180K30Fibre X c) d =
      z180FiveLevelFourierSum X
        (toCRT180 (z180K30LiftFrequency36 d)) c := by
  classical
  let F := z180K30FifthSlice X c
  have hinj : Set.InjOn
      (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (X.filter (fun x ↦ (ZMod.cast x : ZMod 5) = c) : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply z180_k30_cast36_injective_on_fifth_fibre
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy
  calc
    fourierSum (z180K30Fibre X c) d =
        ∑ a ∈ z180K30Fibre X c,
          ZMod.stdAddChar (a * d) := by
      rw [fourierSum]
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (z180K30Fibre X c)
          (fun a ↦ ZMod.stdAddChar (a * d)))
    _ = ∑ x ∈ F,
        ZMod.stdAddChar (z180K30Projection36 x * d) := by
      simp only [F, z180K30FifthSlice, z180K30Projection36_apply]
      rw [z180K30Fibre, Finset.sum_image hinj]
    _ = ∑ x ∈ F,
        z180StandardCRTCharacterPairing (toCRT180 x)
          (toCRT180 (z180K30LiftFrequency36 d)) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        ZMod.stdAddChar (z180K30Projection36 x * d) =
            ZMod.stdAddChar (x * z180K30LiftFrequency36 d) :=
          (z180_stdAddChar_mul_liftFrequency36_eq x d).symm
        _ = ZMod.stdAddChar (z180K30LiftFrequency36 d * x) := by
          rw [mul_comm]
        _ = z180StandardCRTCharacterPairing (toCRT180 x)
            (toCRT180 (z180K30LiftFrequency36 d)) := by
          rw [z180StandardCRTCharacterPairing, ← toCRT180_mul,
            fromCRT180_toCRT180]
    _ = z180FiveLevelFourierSum X
        (toCRT180 (z180K30LiftFrequency36 d)) c := by
      rfl

end Fuglede
