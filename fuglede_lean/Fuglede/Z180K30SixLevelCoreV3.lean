import Fuglede.FourierTiling
import Fuglede.ZModDFTSupport
import Fuglede.Z30K5InflationBridge
import Fuglede.Z180K30ExceptionalBoundary
import Mathlib.Tactic

/-!
# Six-level mixed-radix core for the exceptional K30 branch

This module contains only the coordinate maps and character identities.  The
Fourier summation layer is kept in a separate module so that the finite
coordinate checks remain small and independently replayable.
-/

namespace Fuglede

open scoped BigOperators ZMod

def z180K30Projection6 : ZMod 180 →+ ZMod 6 :=
  (ZMod.castHom (by norm_num : 6 ∣ 180) (ZMod 6)).toAddMonoidHom

@[simp]
theorem z180K30Projection6_apply (x : ZMod 180) :
    z180K30Projection6 x = ZMod.cast x := rfl

def z180K30Kernel30Lift (b : ZMod 6) : ZMod 180 :=
  (30 * b.val : Nat)

def z180K30SixthDigit (x : ZMod 180) : ZMod 30 :=
  (x.val / 6 : Nat)

noncomputable def z180K30SixthFibre
    (X : Finset (ZMod 180)) (c : ZMod 6) : Finset (ZMod 30) :=
  (X.filter fun x ↦ z180K30Projection6 x = c).image z180K30SixthDigit

noncomputable def z180K30SixthSlice
    (X : Finset (ZMod 180)) (c : ZMod 6) : Finset (ZMod 180) :=
  X.filter fun x ↦ z180K30Projection6 x = c

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

theorem z180K30_sixthDigit_reconstruction :
    ∀ x : ZMod 180,
      ((z180K30Projection6 x).val : ZMod 180) +
        z30K5ScaleSix180 (z180K30SixthDigit x) = x := by
  intro x
  fin_cases x <;> decide

theorem z180K30SixthDigit_injective_on_sixth_slice :
    ∀ c : ZMod 6,
      Set.InjOn z180K30SixthDigit
        {x : ZMod 180 | z180K30Projection6 x = c} := by
  intro c x hx y hy hdigit
  rw [← z180K30_sixthDigit_reconstruction x,
    ← z180K30_sixthDigit_reconstruction y, hx, hy, hdigit]

set_option maxRecDepth 100000 in
theorem z180K30_projection30_scaleSix_eq_iff_cast5_eq :
    ∀ q r : ZMod 30,
      z180K30Projection30 (z30K5ScaleSix180 q) =
          z180K30Projection30 (z30K5ScaleSix180 r) ↔
        (ZMod.cast q : ZMod 5) = ZMod.cast r := by
  intro q
  fin_cases q <;> decide

theorem z180K30_projection30_eq_iff_sixthDigit_cast5_eq
    (x y : ZMod 180)
    (hcoord : z180K30Projection6 x = z180K30Projection6 y) :
    z180K30Projection30 x = z180K30Projection30 y ↔
      (ZMod.cast (z180K30SixthDigit x) : ZMod 5) =
        ZMod.cast (z180K30SixthDigit y) := by
  rw [← z180K30_sixthDigit_reconstruction x,
    ← z180K30_sixthDigit_reconstruction y]
  simp only [map_add, hcoord, add_left_inj]
  exact z180K30_projection30_scaleSix_eq_iff_cast5_eq _ _

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

theorem z180_stdAddChar_scaleSix_mul_eq
    (q : ZMod 30) (u : ZMod 180) :
    ZMod.stdAddChar (z30K5ScaleSix180 q * u) =
      ZMod.stdAddChar (q * z180K30Projection30 u) := by
  calc
    ZMod.stdAddChar (z30K5ScaleSix180 q * u) =
        ZMod.stdAddChar
          ((((6 * (q.val : ℤ)) * (u.val : ℤ) : ℤ) : ZMod 180)) := by
      congr 1
      unfold z30K5ScaleSix180
      norm_num [ZMod.natCast_zmod_val]
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
      rw [show z180K30Projection30 u = (ZMod.cast u : ZMod 30) by rfl]
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.cast_eq_val]

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

#print axioms z180K30_projection30_eq_iff_sixthDigit_cast5_eq
#print axioms z180_stdAddChar_eq_sixthDigit_factor

end Fuglede
