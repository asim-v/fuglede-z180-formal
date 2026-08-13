import Fuglede.Z180K18M12PairFibresHighOrder
import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-!
# Structural arithmetic for the `k = 18`, `m = 12`, `q = 45` exclusion

The canonical audit enumerates 54 fifth-level patterns.  For base order
twelve the enumeration has a smaller exact certificate.  A level of size
three whose projected mask is divisible by `Phi_9` has one of three residue
types.  The primitive-twelfth remainder signatures of the three types are
pairwise disjoint: two coordinates vanish and the remaining indicated sum
is odd.  Thus four singleton levels with a common `Phi_12` signature must
have one common type, which is incompatible with global modulo-nine mass
two.

This file contains only the integral/Presburger part of that argument.  The
finite-set and Fourier adapters are kept in the semantic module.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- First coefficient of the primitive-twelfth remainder. -/
def z180K18M12Phi45R0 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 0 - projection36Count12 b 4 -
    projection36Count12 b 6 + projection36Count12 b 10

/-- Second coefficient of the primitive-twelfth remainder. -/
def z180K18M12Phi45R1 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 1 - projection36Count12 b 5 -
    projection36Count12 b 7 + projection36Count12 b 11

/-- Third coefficient of the primitive-twelfth remainder. -/
def z180K18M12Phi45R2 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 2 + projection36Count12 b 4 -
    projection36Count12 b 8 - projection36Count12 b 10

/-- Fourth coefficient of the primitive-twelfth remainder. -/
def z180K18M12Phi45R3 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 3 + projection36Count12 b 5 -
    projection36Count12 b 9 - projection36Count12 b 11

/-- Equality of the four primitive-twelfth remainder coefficients. -/
def Z180K18M12Phi45SameSignature
    (b b' : Fin 36 → Int) : Prop :=
  z180K18M12Phi45R0 b = z180K18M12Phi45R0 b' ∧
    z180K18M12Phi45R1 b = z180K18M12Phi45R1 b' ∧
    z180K18M12Phi45R2 b = z180K18M12Phi45R2 b' ∧
    z180K18M12Phi45R3 b = z180K18M12Phi45R3 b'

/-- The three possible modulo-three types of a size-three `Phi_9` level. -/
def Z180K18M12Phi45RowType
    (b : Fin 36 → Int) (t : Fin 3) : Prop :=
  match t.val with
  | 0 =>
      z180K18M12NineFiberMass b 0 = 1 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 1 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 1 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 0
  | 1 =>
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 1 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 1 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 1 ∧
      z180K18M12NineFiberMass b 8 = 0
  | _ =>
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 1 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 1 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 1

/-- Signature shapes of the three singleton row types.  The existential
equation records oddness without using a finite table. -/
def Z180K18M12Phi45SignatureType
    (b : Fin 36 → Int) (t : Fin 3) : Prop :=
  match t.val with
  | 0 =>
      z180K18M12Phi45R1 b = 0 ∧
      z180K18M12Phi45R2 b = 0 ∧
      ∃ e : Int, z180K18M12Phi45R0 b + z180K18M12Phi45R3 b = 2 * e + 1
  | 1 =>
      z180K18M12Phi45R2 b = -z180K18M12Phi45R0 b ∧
      z180K18M12Phi45R3 b = 0 ∧
      ∃ e : Int, z180K18M12Phi45R0 b + z180K18M12Phi45R1 b = 2 * e + 1
  | _ =>
      z180K18M12Phi45R0 b = 0 ∧
      z180K18M12Phi45R3 b = -z180K18M12Phi45R1 b ∧
      ∃ e : Int, z180K18M12Phi45R1 b + z180K18M12Phi45R2 b = 2 * e + 1

/-- Complete arithmetic profile of one singleton level. -/
def Z180K18M12Phi45SingletonProfile
    (b : Fin 36 → Int) (t : Fin 3) : Prop :=
  Z180K18M12Phi45RowType b t ∧
    Z180K18M12Phi45SignatureType b t

/- Concrete expansion lemmas keep `ZMod.val` and proof-bearing `Fin`
indices out of the Presburger atoms below. -/
@[simp] theorem z180_k18_m12_nineFiberMass_zero (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (0 : ZMod 9) = b 0 + b 9 + b 18 + b 27 := by
  have hv : ZMod.val (0 : ZMod 9) = 0 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_one (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (1 : ZMod 9) = b 1 + b 10 + b 19 + b 28 := by
  have hv : ZMod.val (1 : ZMod 9) = 1 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_two (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (2 : ZMod 9) = b 2 + b 11 + b 20 + b 29 := by
  have hv : ZMod.val (2 : ZMod 9) = 2 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_three (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (3 : ZMod 9) = b 3 + b 12 + b 21 + b 30 := by
  have hv : ZMod.val (3 : ZMod 9) = 3 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_four (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (4 : ZMod 9) = b 4 + b 13 + b 22 + b 31 := by
  have hv : ZMod.val (4 : ZMod 9) = 4 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_five (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (5 : ZMod 9) = b 5 + b 14 + b 23 + b 32 := by
  have hv : ZMod.val (5 : ZMod 9) = 5 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_six (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (6 : ZMod 9) = b 6 + b 15 + b 24 + b 33 := by
  have hv : ZMod.val (6 : ZMod 9) = 6 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_seven (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (7 : ZMod 9) = b 7 + b 16 + b 25 + b 34 := by
  have hv : ZMod.val (7 : ZMod 9) = 7 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_nineFiberMass_eight (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b (8 : ZMod 9) = b 8 + b 17 + b 26 + b 35 := by
  have hv : ZMod.val (8 : ZMod 9) = 8 := by decide
  simp [z180K18M12NineFiberMass, hv]

@[simp] theorem z180_k18_m12_projection36Count12_zero (b : Fin 36 → Int) :
    projection36Count12 b (0 : Fin 12) = b 0 + b 12 + b 24 := by
  change b (0 : Fin 36) + b (12 : Fin 36) + b (24 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_one (b : Fin 36 → Int) :
    projection36Count12 b (1 : Fin 12) = b 1 + b 13 + b 25 := by
  change b (1 : Fin 36) + b (13 : Fin 36) + b (25 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_two (b : Fin 36 → Int) :
    projection36Count12 b (2 : Fin 12) = b 2 + b 14 + b 26 := by
  change b (2 : Fin 36) + b (14 : Fin 36) + b (26 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_three (b : Fin 36 → Int) :
    projection36Count12 b (3 : Fin 12) = b 3 + b 15 + b 27 := by
  change b (3 : Fin 36) + b (15 : Fin 36) + b (27 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_four (b : Fin 36 → Int) :
    projection36Count12 b (4 : Fin 12) = b 4 + b 16 + b 28 := by
  change b (4 : Fin 36) + b (16 : Fin 36) + b (28 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_five (b : Fin 36 → Int) :
    projection36Count12 b (5 : Fin 12) = b 5 + b 17 + b 29 := by
  change b (5 : Fin 36) + b (17 : Fin 36) + b (29 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_six (b : Fin 36 → Int) :
    projection36Count12 b (6 : Fin 12) = b 6 + b 18 + b 30 := by
  change b (6 : Fin 36) + b (18 : Fin 36) + b (30 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_seven (b : Fin 36 → Int) :
    projection36Count12 b (7 : Fin 12) = b 7 + b 19 + b 31 := by
  change b (7 : Fin 36) + b (19 : Fin 36) + b (31 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_eight (b : Fin 36 → Int) :
    projection36Count12 b (8 : Fin 12) = b 8 + b 20 + b 32 := by
  change b (8 : Fin 36) + b (20 : Fin 36) + b (32 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_nine (b : Fin 36 → Int) :
    projection36Count12 b (9 : Fin 12) = b 9 + b 21 + b 33 := by
  change b (9 : Fin 36) + b (21 : Fin 36) + b (33 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_ten (b : Fin 36 → Int) :
    projection36Count12 b (10 : Fin 12) = b 10 + b 22 + b 34 := by
  change b (10 : Fin 36) + b (22 : Fin 36) + b (34 : Fin 36) = _
  rfl

@[simp] theorem z180_k18_m12_projection36Count12_eleven (b : Fin 36 → Int) :
    projection36Count12 b (11 : Fin 12) = b 11 + b 23 + b 35 := by
  change b (11 : Fin 36) + b (23 : Fin 36) + b (35 : Fin 36) = _
  rfl

/-- The nine modulo-nine masses partition all 36 coordinates. -/
theorem z180_k18_m12_nineFiberMass_sum
    (b : Fin 36 → Int) :
    z180K18M12NineFiberMass b 0 +
        z180K18M12NineFiberMass b 1 +
        z180K18M12NineFiberMass b 2 +
        z180K18M12NineFiberMass b 3 +
        z180K18M12NineFiberMass b 4 +
        z180K18M12NineFiberMass b 5 +
        z180K18M12NineFiberMass b 6 +
        z180K18M12NineFiberMass b 7 +
        z180K18M12NineFiberMass b 8 =
      ∑ i : Fin 36, b i := by
  let bn : Nat → Int := fun n ↦
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [bn, Nat.mod_eq_of_lt i.isLt]
  have hbn0 : bn 0 = b 0 := by simpa using hbn (0 : Fin 36)
  have hbn1 : bn 1 = b 1 := by simpa using hbn (1 : Fin 36)
  have hbn2 : bn 2 = b 2 := by simpa using hbn (2 : Fin 36)
  have hbn3 : bn 3 = b 3 := by simpa using hbn (3 : Fin 36)
  have hbn4 : bn 4 = b 4 := by simpa using hbn (4 : Fin 36)
  have hbn5 : bn 5 = b 5 := by simpa using hbn (5 : Fin 36)
  have hbn6 : bn 6 = b 6 := by simpa using hbn (6 : Fin 36)
  have hbn7 : bn 7 = b 7 := by simpa using hbn (7 : Fin 36)
  have hbn8 : bn 8 = b 8 := by simpa using hbn (8 : Fin 36)
  have hbn9 : bn 9 = b 9 := by simpa using hbn (9 : Fin 36)
  have hbn10 : bn 10 = b 10 := by simpa using hbn (10 : Fin 36)
  have hbn11 : bn 11 = b 11 := by simpa using hbn (11 : Fin 36)
  have hbn12 : bn 12 = b 12 := by simpa using hbn (12 : Fin 36)
  have hbn13 : bn 13 = b 13 := by simpa using hbn (13 : Fin 36)
  have hbn14 : bn 14 = b 14 := by simpa using hbn (14 : Fin 36)
  have hbn15 : bn 15 = b 15 := by simpa using hbn (15 : Fin 36)
  have hbn16 : bn 16 = b 16 := by simpa using hbn (16 : Fin 36)
  have hbn17 : bn 17 = b 17 := by simpa using hbn (17 : Fin 36)
  have hbn18 : bn 18 = b 18 := by simpa using hbn (18 : Fin 36)
  have hbn19 : bn 19 = b 19 := by simpa using hbn (19 : Fin 36)
  have hbn20 : bn 20 = b 20 := by simpa using hbn (20 : Fin 36)
  have hbn21 : bn 21 = b 21 := by simpa using hbn (21 : Fin 36)
  have hbn22 : bn 22 = b 22 := by simpa using hbn (22 : Fin 36)
  have hbn23 : bn 23 = b 23 := by simpa using hbn (23 : Fin 36)
  have hbn24 : bn 24 = b 24 := by simpa using hbn (24 : Fin 36)
  have hbn25 : bn 25 = b 25 := by simpa using hbn (25 : Fin 36)
  have hbn26 : bn 26 = b 26 := by simpa using hbn (26 : Fin 36)
  have hbn27 : bn 27 = b 27 := by simpa using hbn (27 : Fin 36)
  have hbn28 : bn 28 = b 28 := by simpa using hbn (28 : Fin 36)
  have hbn29 : bn 29 = b 29 := by simpa using hbn (29 : Fin 36)
  have hbn30 : bn 30 = b 30 := by simpa using hbn (30 : Fin 36)
  have hbn31 : bn 31 = b 31 := by simpa using hbn (31 : Fin 36)
  have hbn32 : bn 32 = b 32 := by simpa using hbn (32 : Fin 36)
  have hbn33 : bn 33 = b 33 := by simpa using hbn (33 : Fin 36)
  have hbn34 : bn 34 = b 34 := by simpa using hbn (34 : Fin 36)
  have hbn35 : bn 35 = b 35 := by simpa using hbn (35 : Fin 36)
  have hsum :
      (∑ i : Fin 36, b i) = ∑ i : Fin 36, bn i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ bn n) 36]
  norm_num [Finset.sum_range_succ]
  simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7,
    hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15,
    hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23,
    hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31,
    hbn32, hbn33, hbn34, hbn35,
    z180_k18_m12_nineFiberMass_zero,
    z180_k18_m12_nineFiberMass_one,
    z180_k18_m12_nineFiberMass_two,
    z180_k18_m12_nineFiberMass_three,
    z180_k18_m12_nineFiberMass_four,
    z180_k18_m12_nineFiberMass_five,
    z180_k18_m12_nineFiberMass_six,
    z180_k18_m12_nineFiberMass_seven,
    z180_k18_m12_nineFiberMass_eight]
  ring

/-- Pointwise nonnegativity implies nonnegativity of every modulo-nine
mass. -/
theorem z180_k18_m12_nineFiberMass_nonneg
    (b : Fin 36 → Int) (hb : ∀ i : Fin 36, 0 ≤ b i) :
    ∀ r : ZMod 9, 0 ≤ z180K18M12NineFiberMass b r := by
  have hb0 := hb (0 : Fin 36)
  have hb1 := hb (1 : Fin 36)
  have hb2 := hb (2 : Fin 36)
  have hb3 := hb (3 : Fin 36)
  have hb4 := hb (4 : Fin 36)
  have hb5 := hb (5 : Fin 36)
  have hb6 := hb (6 : Fin 36)
  have hb7 := hb (7 : Fin 36)
  have hb8 := hb (8 : Fin 36)
  have hb9 := hb (9 : Fin 36)
  have hb10 := hb (10 : Fin 36)
  have hb11 := hb (11 : Fin 36)
  have hb12 := hb (12 : Fin 36)
  have hb13 := hb (13 : Fin 36)
  have hb14 := hb (14 : Fin 36)
  have hb15 := hb (15 : Fin 36)
  have hb16 := hb (16 : Fin 36)
  have hb17 := hb (17 : Fin 36)
  have hb18 := hb (18 : Fin 36)
  have hb19 := hb (19 : Fin 36)
  have hb20 := hb (20 : Fin 36)
  have hb21 := hb (21 : Fin 36)
  have hb22 := hb (22 : Fin 36)
  have hb23 := hb (23 : Fin 36)
  have hb24 := hb (24 : Fin 36)
  have hb25 := hb (25 : Fin 36)
  have hb26 := hb (26 : Fin 36)
  have hb27 := hb (27 : Fin 36)
  have hb28 := hb (28 : Fin 36)
  have hb29 := hb (29 : Fin 36)
  have hb30 := hb (30 : Fin 36)
  have hb31 := hb (31 : Fin 36)
  have hb32 := hb (32 : Fin 36)
  have hb33 := hb (33 : Fin 36)
  have hb34 := hb (34 : Fin 36)
  have hb35 := hb (35 : Fin 36)
  intro r
  fin_cases r
  · change 0 ≤ b 0 + b 9 + b 18 + b 27
    omega
  · change 0 ≤ b 1 + b 10 + b 19 + b 28
    omega
  · change 0 ≤ b 2 + b 11 + b 20 + b 29
    omega
  · change 0 ≤ b 3 + b 12 + b 21 + b 30
    omega
  · change 0 ≤ b 4 + b 13 + b 22 + b 31
    omega
  · change 0 ≤ b 5 + b 14 + b 23 + b 32
    omega
  · change 0 ≤ b 6 + b 15 + b 24 + b 33
    omega
  · change 0 ≤ b 7 + b 16 + b 25 + b 34
    omega
  · change 0 ≤ b 8 + b 17 + b 26 + b 35
    omega

/-- `Phi_9`, total mass three, and nonnegative coefficients force one of
the three singleton row types. -/
theorem z180_k18_m12_phi45_rowType_of_phi9
    (b : Fin 36 → Int)
    (hmass : ∀ r : ZMod 9, 0 ≤ z180K18M12NineFiberMass b r)
    (hsum : (∑ i : Fin 36, b i) = 3)
    (hdiv : cyclotomic 9 Int ∣ projection36IndicatorMask b) :
    ∃ t : Fin 3, Z180K18M12Phi45RowType b t := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := projection36_phi9_remainders b
    (by simpa only [projection36IndicatorMask] using hdiv)
  have heq0 : z180K18M12NineFiberMass b 0 =
      z180K18M12NineFiberMass b 6 := by
    simp only [z180_k18_m12_nineFiberMass_zero,
      z180_k18_m12_nineFiberMass_six]
    omega
  have heq1 : z180K18M12NineFiberMass b 1 =
      z180K18M12NineFiberMass b 7 := by
    simp only [z180_k18_m12_nineFiberMass_one,
      z180_k18_m12_nineFiberMass_seven]
    omega
  have heq2 : z180K18M12NineFiberMass b 2 =
      z180K18M12NineFiberMass b 8 := by
    simp only [z180_k18_m12_nineFiberMass_two,
      z180_k18_m12_nineFiberMass_eight]
    omega
  have heq3 : z180K18M12NineFiberMass b 3 =
      z180K18M12NineFiberMass b 6 := by
    simp only [z180_k18_m12_nineFiberMass_three,
      z180_k18_m12_nineFiberMass_six]
    omega
  have heq4 : z180K18M12NineFiberMass b 4 =
      z180K18M12NineFiberMass b 7 := by
    simp only [z180_k18_m12_nineFiberMass_four,
      z180_k18_m12_nineFiberMass_seven]
    omega
  have heq5 : z180K18M12NineFiberMass b 5 =
      z180K18M12NineFiberMass b 8 := by
    simp only [z180_k18_m12_nineFiberMass_five,
      z180_k18_m12_nineFiberMass_eight]
    omega
  have hmassSum := z180_k18_m12_nineFiberMass_sum b
  rw [hsum] at hmassSum
  have hm0 := hmass (0 : ZMod 9)
  have hm1 := hmass (1 : ZMod 9)
  have hm2 := hmass (2 : ZMod 9)
  have hm3 := hmass (3 : ZMod 9)
  have hm4 := hmass (4 : ZMod 9)
  have hm5 := hmass (5 : ZMod 9)
  have hm6 := hmass (6 : ZMod 9)
  have hm7 := hmass (7 : ZMod 9)
  have hm8 := hmass (8 : ZMod 9)
  have hcases :
      (z180K18M12NineFiberMass b 0 = 1 ∧
        z180K18M12NineFiberMass b 1 = 0 ∧
        z180K18M12NineFiberMass b 2 = 0 ∧
        z180K18M12NineFiberMass b 3 = 1 ∧
        z180K18M12NineFiberMass b 4 = 0 ∧
        z180K18M12NineFiberMass b 5 = 0 ∧
        z180K18M12NineFiberMass b 6 = 1 ∧
        z180K18M12NineFiberMass b 7 = 0 ∧
        z180K18M12NineFiberMass b 8 = 0) ∨
      (z180K18M12NineFiberMass b 0 = 0 ∧
        z180K18M12NineFiberMass b 1 = 1 ∧
        z180K18M12NineFiberMass b 2 = 0 ∧
        z180K18M12NineFiberMass b 3 = 0 ∧
        z180K18M12NineFiberMass b 4 = 1 ∧
        z180K18M12NineFiberMass b 5 = 0 ∧
        z180K18M12NineFiberMass b 6 = 0 ∧
        z180K18M12NineFiberMass b 7 = 1 ∧
        z180K18M12NineFiberMass b 8 = 0) ∨
      (z180K18M12NineFiberMass b 0 = 0 ∧
        z180K18M12NineFiberMass b 1 = 0 ∧
        z180K18M12NineFiberMass b 2 = 1 ∧
        z180K18M12NineFiberMass b 3 = 0 ∧
        z180K18M12NineFiberMass b 4 = 0 ∧
        z180K18M12NineFiberMass b 5 = 1 ∧
        z180K18M12NineFiberMass b 6 = 0 ∧
        z180K18M12NineFiberMass b 7 = 0 ∧
        z180K18M12NineFiberMass b 8 = 1) := by
    omega
  rcases hcases with ht | ht | ht
  · refine ⟨0, ?_⟩
    simpa [Z180K18M12Phi45RowType] using ht
  · refine ⟨1, ?_⟩
    simpa [Z180K18M12Phi45RowType] using ht
  · refine ⟨2, ?_⟩
    simpa [Z180K18M12Phi45RowType] using ht

/-- A row type determines the corresponding primitive-twelfth signature
shape and parity. -/
theorem z180_k18_m12_phi45_signatureType_of_rowType
    (b : Fin 36 → Int) (t : Fin 3)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hrow : Z180K18M12Phi45RowType b t) :
    Z180K18M12Phi45SignatureType b t := by
  have hb0 := hb (0 : Fin 36)
  have hb1 := hb (1 : Fin 36)
  have hb2 := hb (2 : Fin 36)
  have hb3 := hb (3 : Fin 36)
  have hb4 := hb (4 : Fin 36)
  have hb5 := hb (5 : Fin 36)
  have hb6 := hb (6 : Fin 36)
  have hb7 := hb (7 : Fin 36)
  have hb8 := hb (8 : Fin 36)
  have hb9 := hb (9 : Fin 36)
  have hb10 := hb (10 : Fin 36)
  have hb11 := hb (11 : Fin 36)
  have hb12 := hb (12 : Fin 36)
  have hb13 := hb (13 : Fin 36)
  have hb14 := hb (14 : Fin 36)
  have hb15 := hb (15 : Fin 36)
  have hb16 := hb (16 : Fin 36)
  have hb17 := hb (17 : Fin 36)
  have hb18 := hb (18 : Fin 36)
  have hb19 := hb (19 : Fin 36)
  have hb20 := hb (20 : Fin 36)
  have hb21 := hb (21 : Fin 36)
  have hb22 := hb (22 : Fin 36)
  have hb23 := hb (23 : Fin 36)
  have hb24 := hb (24 : Fin 36)
  have hb25 := hb (25 : Fin 36)
  have hb26 := hb (26 : Fin 36)
  have hb27 := hb (27 : Fin 36)
  have hb28 := hb (28 : Fin 36)
  have hb29 := hb (29 : Fin 36)
  have hb30 := hb (30 : Fin 36)
  have hb31 := hb (31 : Fin 36)
  have hb32 := hb (32 : Fin 36)
  have hb33 := hb (33 : Fin 36)
  have hb34 := hb (34 : Fin 36)
  have hb35 := hb (35 : Fin 36)
  fin_cases t
  · change
      z180K18M12NineFiberMass b 0 = 1 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 1 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 1 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 0 at hrow
    simp only [z180_k18_m12_nineFiberMass_zero,
      z180_k18_m12_nineFiberMass_one,
      z180_k18_m12_nineFiberMass_two,
      z180_k18_m12_nineFiberMass_three,
      z180_k18_m12_nineFiberMass_four,
      z180_k18_m12_nineFiberMass_five,
      z180_k18_m12_nineFiberMass_six,
      z180_k18_m12_nineFiberMass_seven,
      z180_k18_m12_nineFiberMass_eight] at hrow
    refine ⟨?_, ?_, ?_⟩
    · simp only [z180K18M12Phi45R1,
        z180_k18_m12_projection36Count12_one,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_seven,
        z180_k18_m12_projection36Count12_eleven]
      omega
    · simp only [z180K18M12Phi45R2,
        z180_k18_m12_projection36Count12_two,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_eight,
        z180_k18_m12_projection36Count12_ten]
      omega
    · refine ⟨1 - projection36Count12 b 6 -
          projection36Count12 b 9, ?_⟩
      simp only [z180K18M12Phi45R0, z180K18M12Phi45R3,
        z180_k18_m12_projection36Count12_zero,
        z180_k18_m12_projection36Count12_three,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_six,
        z180_k18_m12_projection36Count12_nine,
        z180_k18_m12_projection36Count12_ten,
        z180_k18_m12_projection36Count12_eleven]
      omega
  · change
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 1 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 1 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 1 ∧
      z180K18M12NineFiberMass b 8 = 0 at hrow
    simp only [z180_k18_m12_nineFiberMass_zero,
      z180_k18_m12_nineFiberMass_one,
      z180_k18_m12_nineFiberMass_two,
      z180_k18_m12_nineFiberMass_three,
      z180_k18_m12_nineFiberMass_four,
      z180_k18_m12_nineFiberMass_five,
      z180_k18_m12_nineFiberMass_six,
      z180_k18_m12_nineFiberMass_seven,
      z180_k18_m12_nineFiberMass_eight] at hrow
    refine ⟨?_, ?_, ?_⟩
    · simp only [z180K18M12Phi45R0, z180K18M12Phi45R2,
        z180_k18_m12_projection36Count12_zero,
        z180_k18_m12_projection36Count12_two,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_six,
        z180_k18_m12_projection36Count12_eight,
        z180_k18_m12_projection36Count12_ten]
      omega
    · simp only [z180K18M12Phi45R3,
        z180_k18_m12_projection36Count12_three,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_nine,
        z180_k18_m12_projection36Count12_eleven]
      omega
    · refine ⟨1 - projection36Count12 b 4 -
          projection36Count12 b 7, ?_⟩
      simp only [z180K18M12Phi45R0, z180K18M12Phi45R1,
        z180_k18_m12_projection36Count12_zero,
        z180_k18_m12_projection36Count12_one,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_six,
        z180_k18_m12_projection36Count12_seven,
        z180_k18_m12_projection36Count12_ten,
        z180_k18_m12_projection36Count12_eleven]
      omega
  · change
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 1 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 1 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 1 at hrow
    simp only [z180_k18_m12_nineFiberMass_zero,
      z180_k18_m12_nineFiberMass_one,
      z180_k18_m12_nineFiberMass_two,
      z180_k18_m12_nineFiberMass_three,
      z180_k18_m12_nineFiberMass_four,
      z180_k18_m12_nineFiberMass_five,
      z180_k18_m12_nineFiberMass_six,
      z180_k18_m12_nineFiberMass_seven,
      z180_k18_m12_nineFiberMass_eight] at hrow
    refine ⟨?_, ?_, ?_⟩
    · simp only [z180K18M12Phi45R0,
        z180_k18_m12_projection36Count12_zero,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_six,
        z180_k18_m12_projection36Count12_ten]
      omega
    · simp only [z180K18M12Phi45R1, z180K18M12Phi45R3,
        z180_k18_m12_projection36Count12_one,
        z180_k18_m12_projection36Count12_three,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_seven,
        z180_k18_m12_projection36Count12_nine,
        z180_k18_m12_projection36Count12_eleven]
      omega
    · refine ⟨1 - projection36Count12 b 5 -
          projection36Count12 b 8, ?_⟩
      simp only [z180K18M12Phi45R1, z180K18M12Phi45R2,
        z180_k18_m12_projection36Count12_one,
        z180_k18_m12_projection36Count12_two,
        z180_k18_m12_projection36Count12_four,
        z180_k18_m12_projection36Count12_five,
        z180_k18_m12_projection36Count12_seven,
        z180_k18_m12_projection36Count12_eight,
        z180_k18_m12_projection36Count12_ten,
        z180_k18_m12_projection36Count12_eleven]
      omega

/-- Fully package the singleton row profile. -/
theorem z180_k18_m12_phi45_singletonProfile_of_phi9
    (b : Fin 36 → Int)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hsum : (∑ i : Fin 36, b i) = 3)
    (hdiv : cyclotomic 9 Int ∣ projection36IndicatorMask b) :
    ∃ t : Fin 3, Z180K18M12Phi45SingletonProfile b t := by
  have hmass := z180_k18_m12_nineFiberMass_nonneg b hb
  obtain ⟨t, hrow⟩ :=
    z180_k18_m12_phi45_rowType_of_phi9 b hmass hsum hdiv
  refine ⟨t, hrow, ?_⟩
  exact z180_k18_m12_phi45_signatureType_of_rowType b t hb hrow

/-- A `Phi_12` divisor of the difference of two projected masks makes their
four remainder signatures equal. -/
theorem z180_k18_m12_phi45_sameSignature_of_phi12_sub_dvd
    (b b' : Fin 36 → Int)
    (hdiv : cyclotomic 12 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b') :
    Z180K18M12Phi45SameSignature b b' := by
  have hdiv' : cyclotomic 12 Int ∣
      projection36IndicatorMask (fun i ↦ b i - b' i) := by
    rw [projection36IndicatorMask_sub_order20]
    exact hdiv
  obtain ⟨h0, h1, h2, h3⟩ :=
    projection36_phi12_count12_remainders (fun i ↦ b i - b' i)
      (by simpa only [projection36IndicatorMask] using hdiv')
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [z180K18M12Phi45R0, projection36Count12] at h0 ⊢
    omega
  · norm_num [z180K18M12Phi45R1, projection36Count12] at h1 ⊢
    omega
  · norm_num [z180K18M12Phi45R2, projection36Count12] at h2 ⊢
    omega
  · norm_num [z180K18M12Phi45R3, projection36Count12] at h3 ⊢
    omega

/-- The three singleton signature types are pairwise disjoint. -/
theorem z180_k18_m12_phi45_type_eq_of_sameSignature
    (b b' : Fin 36 → Int) (t t' : Fin 3)
    (ht : Z180K18M12Phi45SignatureType b t)
    (ht' : Z180K18M12Phi45SignatureType b' t')
    (hsame : Z180K18M12Phi45SameSignature b b') :
    t = t' := by
  rcases hsame with ⟨hR0, hR1, hR2, hR3⟩
  fin_cases t <;> fin_cases t' <;>
    norm_num [Z180K18M12Phi45SignatureType] at ht ht' ⊢ <;>
    rcases ht with ⟨ht0, ht1, et, htodd⟩ <;>
    rcases ht' with ⟨ht0', ht1', et', htodd'⟩ <;>
    omega

/-- Four singleton profiles with a common signature cannot fit into global
modulo-nine mass two.  The fifth row is used only through nonnegativity. -/
theorem z180_k18_m12_phi45_four_singletons_impossible
    (b0 b1 b2 b3 b4 bg : Fin 36 → Int)
    (hp0 : ∃ t : Fin 3, Z180K18M12Phi45SingletonProfile b0 t)
    (hp1 : ∃ t : Fin 3, Z180K18M12Phi45SingletonProfile b1 t)
    (hp2 : ∃ t : Fin 3, Z180K18M12Phi45SingletonProfile b2 t)
    (hp3 : ∃ t : Fin 3, Z180K18M12Phi45SingletonProfile b3 t)
    (hs01 : Z180K18M12Phi45SameSignature b0 b1)
    (hs02 : Z180K18M12Phi45SameSignature b0 b2)
    (hs03 : Z180K18M12Phi45SameSignature b0 b3)
    (hmass4 : ∀ r : ZMod 9, 0 ≤ z180K18M12NineFiberMass b4 r)
    (hmassSum : ∀ r : ZMod 9,
      z180K18M12NineFiberMass b0 r +
          z180K18M12NineFiberMass b1 r +
          z180K18M12NineFiberMass b2 r +
          z180K18M12NineFiberMass b3 r +
          z180K18M12NineFiberMass b4 r =
        z180K18M12NineFiberMass bg r)
    (hglobal : ∀ r : ZMod 9,
      z180K18M12NineFiberMass bg r = 2) : False := by
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b0 t ∧
    Z180K18M12Phi45SignatureType b0 t at hp0
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b1 t ∧
    Z180K18M12Phi45SignatureType b1 t at hp1
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b2 t ∧
    Z180K18M12Phi45SignatureType b2 t at hp2
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b3 t ∧
    Z180K18M12Phi45SignatureType b3 t at hp3
  obtain ⟨t0, hrow0, hsig0⟩ := hp0
  obtain ⟨t1, hrow1, hsig1⟩ := hp1
  obtain ⟨t2, hrow2, hsig2⟩ := hp2
  obtain ⟨t3, hrow3, hsig3⟩ := hp3
  have ht01 := z180_k18_m12_phi45_type_eq_of_sameSignature
    b0 b1 t0 t1 hsig0 hsig1 hs01
  have ht02 := z180_k18_m12_phi45_type_eq_of_sameSignature
    b0 b2 t0 t2 hsig0 hsig2 hs02
  have ht03 := z180_k18_m12_phi45_type_eq_of_sameSignature
    b0 b3 t0 t3 hsig0 hsig3 hs03
  subst t1
  subst t2
  subst t3
  fin_cases t0
  · change
      z180K18M12NineFiberMass b0 0 = 1 ∧
      z180K18M12NineFiberMass b0 1 = 0 ∧
      z180K18M12NineFiberMass b0 2 = 0 ∧
      z180K18M12NineFiberMass b0 3 = 1 ∧
      z180K18M12NineFiberMass b0 4 = 0 ∧
      z180K18M12NineFiberMass b0 5 = 0 ∧
      z180K18M12NineFiberMass b0 6 = 1 ∧
      z180K18M12NineFiberMass b0 7 = 0 ∧
      z180K18M12NineFiberMass b0 8 = 0 at hrow0
    change
      z180K18M12NineFiberMass b1 0 = 1 ∧
      z180K18M12NineFiberMass b1 1 = 0 ∧
      z180K18M12NineFiberMass b1 2 = 0 ∧
      z180K18M12NineFiberMass b1 3 = 1 ∧
      z180K18M12NineFiberMass b1 4 = 0 ∧
      z180K18M12NineFiberMass b1 5 = 0 ∧
      z180K18M12NineFiberMass b1 6 = 1 ∧
      z180K18M12NineFiberMass b1 7 = 0 ∧
      z180K18M12NineFiberMass b1 8 = 0 at hrow1
    change
      z180K18M12NineFiberMass b2 0 = 1 ∧
      z180K18M12NineFiberMass b2 1 = 0 ∧
      z180K18M12NineFiberMass b2 2 = 0 ∧
      z180K18M12NineFiberMass b2 3 = 1 ∧
      z180K18M12NineFiberMass b2 4 = 0 ∧
      z180K18M12NineFiberMass b2 5 = 0 ∧
      z180K18M12NineFiberMass b2 6 = 1 ∧
      z180K18M12NineFiberMass b2 7 = 0 ∧
      z180K18M12NineFiberMass b2 8 = 0 at hrow2
    change
      z180K18M12NineFiberMass b3 0 = 1 ∧
      z180K18M12NineFiberMass b3 1 = 0 ∧
      z180K18M12NineFiberMass b3 2 = 0 ∧
      z180K18M12NineFiberMass b3 3 = 1 ∧
      z180K18M12NineFiberMass b3 4 = 0 ∧
      z180K18M12NineFiberMass b3 5 = 0 ∧
      z180K18M12NineFiberMass b3 6 = 1 ∧
      z180K18M12NineFiberMass b3 7 = 0 ∧
      z180K18M12NineFiberMass b3 8 = 0 at hrow3
    have h4 := hmass4 (0 : ZMod 9)
    have hsum := hmassSum (0 : ZMod 9)
    have hg := hglobal (0 : ZMod 9)
    omega
  · change
      z180K18M12NineFiberMass b0 0 = 0 ∧
      z180K18M12NineFiberMass b0 1 = 1 ∧
      z180K18M12NineFiberMass b0 2 = 0 ∧
      z180K18M12NineFiberMass b0 3 = 0 ∧
      z180K18M12NineFiberMass b0 4 = 1 ∧
      z180K18M12NineFiberMass b0 5 = 0 ∧
      z180K18M12NineFiberMass b0 6 = 0 ∧
      z180K18M12NineFiberMass b0 7 = 1 ∧
      z180K18M12NineFiberMass b0 8 = 0 at hrow0
    change
      z180K18M12NineFiberMass b1 0 = 0 ∧
      z180K18M12NineFiberMass b1 1 = 1 ∧
      z180K18M12NineFiberMass b1 2 = 0 ∧
      z180K18M12NineFiberMass b1 3 = 0 ∧
      z180K18M12NineFiberMass b1 4 = 1 ∧
      z180K18M12NineFiberMass b1 5 = 0 ∧
      z180K18M12NineFiberMass b1 6 = 0 ∧
      z180K18M12NineFiberMass b1 7 = 1 ∧
      z180K18M12NineFiberMass b1 8 = 0 at hrow1
    change
      z180K18M12NineFiberMass b2 0 = 0 ∧
      z180K18M12NineFiberMass b2 1 = 1 ∧
      z180K18M12NineFiberMass b2 2 = 0 ∧
      z180K18M12NineFiberMass b2 3 = 0 ∧
      z180K18M12NineFiberMass b2 4 = 1 ∧
      z180K18M12NineFiberMass b2 5 = 0 ∧
      z180K18M12NineFiberMass b2 6 = 0 ∧
      z180K18M12NineFiberMass b2 7 = 1 ∧
      z180K18M12NineFiberMass b2 8 = 0 at hrow2
    change
      z180K18M12NineFiberMass b3 0 = 0 ∧
      z180K18M12NineFiberMass b3 1 = 1 ∧
      z180K18M12NineFiberMass b3 2 = 0 ∧
      z180K18M12NineFiberMass b3 3 = 0 ∧
      z180K18M12NineFiberMass b3 4 = 1 ∧
      z180K18M12NineFiberMass b3 5 = 0 ∧
      z180K18M12NineFiberMass b3 6 = 0 ∧
      z180K18M12NineFiberMass b3 7 = 1 ∧
      z180K18M12NineFiberMass b3 8 = 0 at hrow3
    have h4 := hmass4 (1 : ZMod 9)
    have hsum := hmassSum (1 : ZMod 9)
    have hg := hglobal (1 : ZMod 9)
    omega
  · change
      z180K18M12NineFiberMass b0 0 = 0 ∧
      z180K18M12NineFiberMass b0 1 = 0 ∧
      z180K18M12NineFiberMass b0 2 = 1 ∧
      z180K18M12NineFiberMass b0 3 = 0 ∧
      z180K18M12NineFiberMass b0 4 = 0 ∧
      z180K18M12NineFiberMass b0 5 = 1 ∧
      z180K18M12NineFiberMass b0 6 = 0 ∧
      z180K18M12NineFiberMass b0 7 = 0 ∧
      z180K18M12NineFiberMass b0 8 = 1 at hrow0
    change
      z180K18M12NineFiberMass b1 0 = 0 ∧
      z180K18M12NineFiberMass b1 1 = 0 ∧
      z180K18M12NineFiberMass b1 2 = 1 ∧
      z180K18M12NineFiberMass b1 3 = 0 ∧
      z180K18M12NineFiberMass b1 4 = 0 ∧
      z180K18M12NineFiberMass b1 5 = 1 ∧
      z180K18M12NineFiberMass b1 6 = 0 ∧
      z180K18M12NineFiberMass b1 7 = 0 ∧
      z180K18M12NineFiberMass b1 8 = 1 at hrow1
    change
      z180K18M12NineFiberMass b2 0 = 0 ∧
      z180K18M12NineFiberMass b2 1 = 0 ∧
      z180K18M12NineFiberMass b2 2 = 1 ∧
      z180K18M12NineFiberMass b2 3 = 0 ∧
      z180K18M12NineFiberMass b2 4 = 0 ∧
      z180K18M12NineFiberMass b2 5 = 1 ∧
      z180K18M12NineFiberMass b2 6 = 0 ∧
      z180K18M12NineFiberMass b2 7 = 0 ∧
      z180K18M12NineFiberMass b2 8 = 1 at hrow2
    change
      z180K18M12NineFiberMass b3 0 = 0 ∧
      z180K18M12NineFiberMass b3 1 = 0 ∧
      z180K18M12NineFiberMass b3 2 = 1 ∧
      z180K18M12NineFiberMass b3 3 = 0 ∧
      z180K18M12NineFiberMass b3 4 = 0 ∧
      z180K18M12NineFiberMass b3 5 = 1 ∧
      z180K18M12NineFiberMass b3 6 = 0 ∧
      z180K18M12NineFiberMass b3 7 = 0 ∧
      z180K18M12NineFiberMass b3 8 = 1 at hrow3
    have h4 := hmass4 (2 : ZMod 9)
    have hsum := hmassSum (2 : ZMod 9)
    have hg := hglobal (2 : ZMod 9)
    omega

/-- Five positive multiples of three summing to eighteen consist of one six
and four threes. -/
theorem z180_k18_m12_phi45_level_size_cases
    (s0 s1 s2 s3 s4 t0 t1 t2 t3 t4 : Nat)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hs3 : 0 < s3) (hs4 : 0 < s4)
    (ht0 : s0 = 3 * t0) (ht1 : s1 = 3 * t1)
    (ht2 : s2 = 3 * t2) (ht3 : s3 = 3 * t3)
    (ht4 : s4 = 3 * t4)
    (hsum : s0 + s1 + s2 + s3 + s4 = 18) :
    (s0 = 6 ∧ s1 = 3 ∧ s2 = 3 ∧ s3 = 3 ∧ s4 = 3) ∨
    (s0 = 3 ∧ s1 = 6 ∧ s2 = 3 ∧ s3 = 3 ∧ s4 = 3) ∨
    (s0 = 3 ∧ s1 = 3 ∧ s2 = 6 ∧ s3 = 3 ∧ s4 = 3) ∨
    (s0 = 3 ∧ s1 = 3 ∧ s2 = 3 ∧ s3 = 6 ∧ s4 = 3) ∨
    (s0 = 3 ∧ s1 = 3 ∧ s2 = 3 ∧ s3 = 3 ∧ s4 = 6) := by
  omega

#print axioms z180_k18_m12_nineFiberMass_sum
#print axioms z180_k18_m12_phi45_singletonProfile_of_phi9
#print axioms z180_k18_m12_phi45_sameSignature_of_phi12_sub_dvd
#print axioms z180_k18_m12_phi45_type_eq_of_sameSignature
#print axioms z180_k18_m12_phi45_four_singletons_impossible
#print axioms z180_k18_m12_phi45_level_size_cases

end Fuglede
