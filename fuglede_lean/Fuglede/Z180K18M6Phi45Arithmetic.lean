import Fuglede.Z180K18M12Phi45Arithmetic
import Mathlib.Tactic

/-!
# Structural arithmetic for the `k = 18`, `m = 6`, `q = 45` exclusion

The `Phi_9` singleton-row classification is shared with the base-order
twelve argument.  At primitive order six the three row types have signatures
`(odd,0)`, `(0,odd)`, and `(odd,-odd)`, so their exact value sets are again
pairwise disjoint.  This module packages that smaller certificate without
enumerating the canonical 54 level patterns.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Equality of the two primitive-six projected remainders. -/
def Z180K18M6Phi45SameSignature
    (b b' : Fin 36 → Int) : Prop :=
  projection36Phi6R0 b = projection36Phi6R0 b' ∧
    projection36Phi6R1 b = projection36Phi6R1 b'

/-- Signature shape and parity for one of the three singleton row types. -/
def Z180K18M6Phi45SignatureType
    (b : Fin 36 → Int) (t : Fin 3) : Prop :=
  match t.val with
  | 0 =>
      projection36Phi6R1 b = 0 ∧
      ∃ e : Int, projection36Phi6R0 b = 2 * e + 1
  | 1 =>
      projection36Phi6R0 b = 0 ∧
      ∃ e : Int, projection36Phi6R1 b = 2 * e + 1
  | _ =>
      projection36Phi6R1 b = -projection36Phi6R0 b ∧
      ∃ e : Int, projection36Phi6R0 b = 2 * e + 1

def Z180K18M6Phi45SingletonProfile
    (b : Fin 36 → Int) (t : Fin 3) : Prop :=
  Z180K18M12Phi45RowType b t ∧
    Z180K18M6Phi45SignatureType b t

private theorem z180_k18_m6_phi45_four_coordinates_le_one
    (a b c d : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d ≤ 1) :
    a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 := by
  omega

private theorem z180_k18_m6_phi45_le_one_of_eq
    (a s : Int) (h : a = s) (hs : s ≤ 1) : a ≤ 1 := by
  omega

private theorem z180_k18_m6_phi45_coordinates_le_one
    (b : Fin 36 → Int)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hm0 : b 0 + b 9 + b 18 + b 27 ≤ 1)
    (hm1 : b 1 + b 10 + b 19 + b 28 ≤ 1)
    (hm2 : b 2 + b 11 + b 20 + b 29 ≤ 1)
    (hm3 : b 3 + b 12 + b 21 + b 30 ≤ 1)
    (hm4 : b 4 + b 13 + b 22 + b 31 ≤ 1)
    (hm5 : b 5 + b 14 + b 23 + b 32 ≤ 1)
    (hm6 : b 6 + b 15 + b 24 + b 33 ≤ 1)
    (hm7 : b 7 + b 16 + b 25 + b 34 ≤ 1)
    (hm8 : b 8 + b 17 + b 26 + b 35 ≤ 1) :
    ∀ i : Fin 36, b i ≤ 1 := by
  obtain ⟨hb0, hb9, hb18, hb27⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 0) (b 9) (b 18) (b 27)
      (hb 0) (hb 9) (hb 18) (hb 27) hm0
  obtain ⟨hb1, hb10, hb19, hb28⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 1) (b 10) (b 19) (b 28)
      (hb 1) (hb 10) (hb 19) (hb 28) hm1
  obtain ⟨hb2, hb11, hb20, hb29⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 2) (b 11) (b 20) (b 29)
      (hb 2) (hb 11) (hb 20) (hb 29) hm2
  obtain ⟨hb3, hb12, hb21, hb30⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 3) (b 12) (b 21) (b 30)
      (hb 3) (hb 12) (hb 21) (hb 30) hm3
  obtain ⟨hb4, hb13, hb22, hb31⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 4) (b 13) (b 22) (b 31)
      (hb 4) (hb 13) (hb 22) (hb 31) hm4
  obtain ⟨hb5, hb14, hb23, hb32⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 5) (b 14) (b 23) (b 32)
      (hb 5) (hb 14) (hb 23) (hb 32) hm5
  obtain ⟨hb6, hb15, hb24, hb33⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 6) (b 15) (b 24) (b 33)
      (hb 6) (hb 15) (hb 24) (hb 33) hm6
  obtain ⟨hb7, hb16, hb25, hb34⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 7) (b 16) (b 25) (b 34)
      (hb 7) (hb 16) (hb 25) (hb 34) hm7
  obtain ⟨hb8, hb17, hb26, hb35⟩ :=
    z180_k18_m6_phi45_four_coordinates_le_one
      (b 8) (b 17) (b 26) (b 35)
      (hb 8) (hb 17) (hb 26) (hb 35) hm8
  intro i
  fin_cases i <;> assumption

/-- A singleton row type determines its primitive-six signature shape. -/
private theorem z180_k18_m6_phi45_signatureType_of_rowType_of_le_one
    (b : Fin 36 → Int) (t : Fin 3)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hbi : ∀ i : Fin 36, b i ≤ 1)
    (hrow : Z180K18M12Phi45RowType b t) :
    Z180K18M6Phi45SignatureType b t := by
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
  have hb0hi := hbi (0 : Fin 36)
  have hb1hi := hbi (1 : Fin 36)
  have hb2hi := hbi (2 : Fin 36)
  have hb3hi := hbi (3 : Fin 36)
  have hb4hi := hbi (4 : Fin 36)
  have hb5hi := hbi (5 : Fin 36)
  have hb6hi := hbi (6 : Fin 36)
  have hb7hi := hbi (7 : Fin 36)
  have hb8hi := hbi (8 : Fin 36)
  have hb9hi := hbi (9 : Fin 36)
  have hb10hi := hbi (10 : Fin 36)
  have hb11hi := hbi (11 : Fin 36)
  have hb12hi := hbi (12 : Fin 36)
  have hb13hi := hbi (13 : Fin 36)
  have hb14hi := hbi (14 : Fin 36)
  have hb15hi := hbi (15 : Fin 36)
  have hb16hi := hbi (16 : Fin 36)
  have hb17hi := hbi (17 : Fin 36)
  have hb18hi := hbi (18 : Fin 36)
  have hb19hi := hbi (19 : Fin 36)
  have hb20hi := hbi (20 : Fin 36)
  have hb21hi := hbi (21 : Fin 36)
  have hb22hi := hbi (22 : Fin 36)
  have hb23hi := hbi (23 : Fin 36)
  have hb24hi := hbi (24 : Fin 36)
  have hb25hi := hbi (25 : Fin 36)
  have hb26hi := hbi (26 : Fin 36)
  have hb27hi := hbi (27 : Fin 36)
  have hb28hi := hbi (28 : Fin 36)
  have hb29hi := hbi (29 : Fin 36)
  have hb30hi := hbi (30 : Fin 36)
  have hb31hi := hbi (31 : Fin 36)
  have hb32hi := hbi (32 : Fin 36)
  have hb33hi := hbi (33 : Fin 36)
  have hb34hi := hbi (34 : Fin 36)
  have hb35hi := hbi (35 : Fin 36)
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
    refine ⟨?_, ?_⟩
    · norm_num [projection36Phi6R1]
      omega
    · refine ⟨1 - (b 3 + b 9 + b 15 + b 21 + b 27 + b 33), ?_⟩
      norm_num [projection36Phi6R0]
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
    refine ⟨?_, ?_⟩
    · norm_num [projection36Phi6R0]
      omega
    · refine ⟨1 - (b 4 + b 10 + b 16 + b 22 + b 28 + b 34), ?_⟩
      norm_num [projection36Phi6R1]
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
    refine ⟨?_, ?_⟩
    · norm_num [projection36Phi6R0, projection36Phi6R1]
      omega
    · refine ⟨1 - (b 2 + b 8 + b 14 + b 20 + b 26 + b 32), ?_⟩
      norm_num [projection36Phi6R0]
      omega

/-- A singleton row type determines its primitive-six signature shape. -/
theorem z180_k18_m6_phi45_signatureType_of_rowType
    (b : Fin 36 → Int) (t : Fin 3)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hrow : Z180K18M12Phi45RowType b t) :
    Z180K18M6Phi45SignatureType b t := by
  fin_cases t
  · have hr := hrow
    norm_num [Z180K18M12Phi45RowType,
      z180K18M12NineFiberMass] at hr
    rcases hr with ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8⟩
    have hbi := z180_k18_m6_phi45_coordinates_le_one b hb
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm0 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm1 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm2 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm3 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm4 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm5 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm6 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm7 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm8 (by norm_num))
    exact z180_k18_m6_phi45_signatureType_of_rowType_of_le_one
      b 0 hb hbi hrow
  · have hr := hrow
    norm_num [Z180K18M12Phi45RowType,
      z180K18M12NineFiberMass] at hr
    rcases hr with ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8⟩
    have hbi := z180_k18_m6_phi45_coordinates_le_one b hb
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm0 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm1 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm2 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm3 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm4 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm5 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm6 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm7 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm8 (by norm_num))
    exact z180_k18_m6_phi45_signatureType_of_rowType_of_le_one
      b 1 hb hbi hrow
  · have hr := hrow
    norm_num [Z180K18M12Phi45RowType,
      z180K18M12NineFiberMass] at hr
    rcases hr with ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8⟩
    have hbi := z180_k18_m6_phi45_coordinates_le_one b hb
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm0 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm1 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm2 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm3 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm4 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm5 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm6 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 0 hm7 (by norm_num))
      (z180_k18_m6_phi45_le_one_of_eq _ 1 hm8 (by norm_num))
    exact z180_k18_m6_phi45_signatureType_of_rowType_of_le_one
      b 2 hb hbi hrow

theorem z180_k18_m6_phi45_singletonProfile_of_phi9
    (b : Fin 36 → Int)
    (hb : ∀ i : Fin 36, 0 ≤ b i)
    (hsum : (∑ i : Fin 36, b i) = 3)
    (hdiv : cyclotomic 9 Int ∣ projection36IndicatorMask b) :
    ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile b t := by
  have hmass := z180_k18_m12_nineFiberMass_nonneg b hb
  obtain ⟨t, hrow⟩ :=
    z180_k18_m12_phi45_rowType_of_phi9 b hmass hsum hdiv
  refine ⟨t, hrow, ?_⟩
  exact z180_k18_m6_phi45_signatureType_of_rowType b t hb hrow

/-- A `Phi_6` divisor of a mask difference makes the two signatures equal. -/
theorem z180_k18_m6_phi45_sameSignature_of_phi6_sub_dvd
    (b b' : Fin 36 → Int)
    (hdiv : cyclotomic 6 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b') :
    Z180K18M6Phi45SameSignature b b' := by
  have hdiv' : cyclotomic 6 Int ∣
      projection36IndicatorMask (fun i ↦ b i - b' i) := by
    rw [projection36IndicatorMask_sub_order20]
    exact hdiv
  obtain ⟨h0, h1⟩ :=
    (projection36_phi6_dvd_iff_remainders_zero
      (fun i ↦ b i - b' i)).1 hdiv'
  refine ⟨?_, ?_⟩
  · norm_num [projection36Phi6R0] at h0 ⊢
    omega
  · norm_num [projection36Phi6R1] at h1 ⊢
    omega

/-- The primitive-six singleton signature types are pairwise disjoint. -/
theorem z180_k18_m6_phi45_type_eq_of_sameSignature
    (b b' : Fin 36 → Int) (t t' : Fin 3)
    (ht : Z180K18M6Phi45SignatureType b t)
    (ht' : Z180K18M6Phi45SignatureType b' t')
    (hsame : Z180K18M6Phi45SameSignature b b') :
    t = t' := by
  rcases hsame with ⟨hR0, hR1⟩
  fin_cases t <;> fin_cases t' <;>
    norm_num [Z180K18M6Phi45SignatureType] at ht ht' ⊢ <;>
    rcases ht with ⟨ht0, et, htodd⟩ <;>
    rcases ht' with ⟨ht0', et', htodd'⟩ <;>
    omega

private theorem z180_k18_m6_phi45_selected_mass_one
    (b : Fin 36 → Int) (t : Fin 3)
    (hrow : Z180K18M12Phi45RowType b t) :
    z180K18M12NineFiberMass b (t.val : ZMod 9) = 1 := by
  fin_cases t
  · change z180K18M12NineFiberMass b 0 = 1
    change
      z180K18M12NineFiberMass b 0 = 1 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 1 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 1 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 0 at hrow
    exact hrow.1
  · change z180K18M12NineFiberMass b 1 = 1
    change
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 1 ∧
      z180K18M12NineFiberMass b 2 = 0 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 1 ∧
      z180K18M12NineFiberMass b 5 = 0 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 1 ∧
      z180K18M12NineFiberMass b 8 = 0 at hrow
    exact hrow.2.1
  · change z180K18M12NineFiberMass b 2 = 1
    change
      z180K18M12NineFiberMass b 0 = 0 ∧
      z180K18M12NineFiberMass b 1 = 0 ∧
      z180K18M12NineFiberMass b 2 = 1 ∧
      z180K18M12NineFiberMass b 3 = 0 ∧
      z180K18M12NineFiberMass b 4 = 0 ∧
      z180K18M12NineFiberMass b 5 = 1 ∧
      z180K18M12NineFiberMass b 6 = 0 ∧
      z180K18M12NineFiberMass b 7 = 0 ∧
      z180K18M12NineFiberMass b 8 = 1 at hrow
    exact hrow.2.2.1

private theorem z180_k18_m6_phi45_four_masses_impossible
    (a0 a1 a2 a3 a4 g : Int)
    (h0 : a0 = 1) (h1 : a1 = 1) (h2 : a2 = 1) (h3 : a3 = 1)
    (h4 : 0 ≤ a4) (hsum : a0 + a1 + a2 + a3 + a4 = g)
    (hg : g = 2) : False := by
  omega

/-- Four singleton profiles with a common primitive-six signature cannot
fit into global modulo-nine mass two. -/
theorem z180_k18_m6_phi45_four_singletons_impossible
    (b0 b1 b2 b3 b4 bg : Fin 36 → Int)
    (hp0 : ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile b0 t)
    (hp1 : ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile b1 t)
    (hp2 : ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile b2 t)
    (hp3 : ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile b3 t)
    (hs01 : Z180K18M6Phi45SameSignature b0 b1)
    (hs02 : Z180K18M6Phi45SameSignature b0 b2)
    (hs03 : Z180K18M6Phi45SameSignature b0 b3)
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
    Z180K18M6Phi45SignatureType b0 t at hp0
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b1 t ∧
    Z180K18M6Phi45SignatureType b1 t at hp1
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b2 t ∧
    Z180K18M6Phi45SignatureType b2 t at hp2
  change ∃ t : Fin 3, Z180K18M12Phi45RowType b3 t ∧
    Z180K18M6Phi45SignatureType b3 t at hp3
  obtain ⟨t0, hrow0, hsig0⟩ := hp0
  obtain ⟨t1, hrow1, hsig1⟩ := hp1
  obtain ⟨t2, hrow2, hsig2⟩ := hp2
  obtain ⟨t3, hrow3, hsig3⟩ := hp3
  have ht01 := z180_k18_m6_phi45_type_eq_of_sameSignature
    b0 b1 t0 t1 hsig0 hsig1 hs01
  have ht02 := z180_k18_m6_phi45_type_eq_of_sameSignature
    b0 b2 t0 t2 hsig0 hsig2 hs02
  have ht03 := z180_k18_m6_phi45_type_eq_of_sameSignature
    b0 b3 t0 t3 hsig0 hsig3 hs03
  subst t1
  subst t2
  subst t3
  fin_cases t0
  · have hb0one : z180K18M12NineFiberMass b0 (0 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b0 0 hrow0
    have hb1one : z180K18M12NineFiberMass b1 (0 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b1 0 hrow1
    have hb2one : z180K18M12NineFiberMass b2 (0 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b2 0 hrow2
    have hb3one : z180K18M12NineFiberMass b3 (0 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b3 0 hrow3
    have h4 := hmass4 (0 : ZMod 9)
    have hsum := hmassSum (0 : ZMod 9)
    have hg := hglobal (0 : ZMod 9)
    exact z180_k18_m6_phi45_four_masses_impossible
      _ _ _ _ _ _ hb0one hb1one hb2one hb3one h4 hsum hg
  · have hb0one : z180K18M12NineFiberMass b0 (1 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b0 1 hrow0
    have hb1one : z180K18M12NineFiberMass b1 (1 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b1 1 hrow1
    have hb2one : z180K18M12NineFiberMass b2 (1 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b2 1 hrow2
    have hb3one : z180K18M12NineFiberMass b3 (1 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b3 1 hrow3
    have h4 := hmass4 (1 : ZMod 9)
    have hsum := hmassSum (1 : ZMod 9)
    have hg := hglobal (1 : ZMod 9)
    exact z180_k18_m6_phi45_four_masses_impossible
      _ _ _ _ _ _ hb0one hb1one hb2one hb3one h4 hsum hg
  · have hb0one : z180K18M12NineFiberMass b0 (2 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b0 2 hrow0
    have hb1one : z180K18M12NineFiberMass b1 (2 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b1 2 hrow1
    have hb2one : z180K18M12NineFiberMass b2 (2 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b2 2 hrow2
    have hb3one : z180K18M12NineFiberMass b3 (2 : ZMod 9) = 1 := by
      simpa using z180_k18_m6_phi45_selected_mass_one b3 2 hrow3
    have h4 := hmass4 (2 : ZMod 9)
    have hsum := hmassSum (2 : ZMod 9)
    have hg := hglobal (2 : ZMod 9)
    exact z180_k18_m6_phi45_four_masses_impossible
      _ _ _ _ _ _ hb0one hb1one hb2one hb3one h4 hsum hg

#print axioms z180_k18_m6_phi45_signatureType_of_rowType
#print axioms z180_k18_m6_phi45_singletonProfile_of_phi9
#print axioms z180_k18_m6_phi45_sameSignature_of_phi6_sub_dvd
#print axioms z180_k18_m6_phi45_type_eq_of_sameSignature
#print axioms z180_k18_m6_phi45_four_singletons_impossible

end Fuglede
