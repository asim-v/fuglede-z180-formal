import Fuglede.FourierTiling
import Fuglede.ExactOrderDistribution
import Mathlib.Tactic

/-!
# Fixed Fourier covers for the two low cardinality-eighteen branches

The finite terminal audit for `ZMod 180`, cardinality eighteen, leaves four
low-order profiles.  This file contains only the exact algebraic endpoint of
those four routes: the four concrete ten-point complements, their complete
cyclotomic zero signatures, and the resulting tiling theorems.

No envelope or clique census is asserted here, and none of the extra
set-side zeros is inferred.  Those hypotheses remain visible in the four
route signatures below.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Divisibility at a named character order, independent of a representative
frequency having that order. -/
def Z180K18OrderZero (A : Finset (ZMod 180)) (q : Nat) : Prop :=
  cyclotomic q Int ∣ maskPolynomial 180 A

/-- Simultaneous set-side zeros on a finite order signature. -/
def Z180K18OrderZerosOn
    (A : Finset (ZMod 180)) (orders : Finset Nat) : Prop :=
  ∀ q ∈ orders, Z180K18OrderZero A q

theorem z180_k18_orderZerosOn_union
    {A : Finset (ZMod 180)} {S T : Finset Nat}
    (hS : Z180K18OrderZerosOn A S)
    (hT : Z180K18OrderZerosOn A T) :
    Z180K18OrderZerosOn A (S ∪ T) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hqS | hqT
  · exact hS q hqS
  · exact hT q hqT

/-- The first exact `m = 2` difference-order profile. -/
def z180K18M2ProfileOneOrders : Finset Nat :=
  {3, 9, 20, 60, 180}

/-- The second exact `m = 2` difference-order profile. -/
def z180K18M2ProfileTwoOrders : Finset Nat :=
  {3, 4, 9, 12, 36}

/-- The first feasible `m = 4` difference-order profile. -/
def z180K18M4ProfileOneOrders : Finset Nat :=
  {3, 9, 10, 30, 90}

/-- The second feasible `m = 4` difference-order profile. -/
def z180K18M4ProfileTwoOrders : Finset Nat :=
  {2, 3, 6, 9, 18}

/-- The three extra zeros in the first `m = 2` route. -/
def z180K18M2ProfileOneExtraOrders : Finset Nat :=
  {4, 12, 36}

/-- The three extra zeros in the first `m = 4` route. -/
def z180K18M4ProfileOneExtraOrders : Finset Nat :=
  {2, 6, 18}

/-- Complete set-side signature used by the first `m = 2` cover.  Order ten
is the high zero supplied directly by the defect. -/
def z180K18M2RouteOneOrders : Finset Nat :=
  (z180K18M2ProfileOneOrders ∪ {10}) ∪
    z180K18M2ProfileOneExtraOrders

/-- Complete set-side signature used by the second `m = 2` cover. -/
def z180K18M2RouteTwoOrders : Finset Nat :=
  z180K18M2ProfileTwoOrders ∪ {10}

/-- Complete set-side signature used by the first `m = 4` cover.  Order
twenty is the high zero supplied directly by the defect. -/
def z180K18M4RouteOneOrders : Finset Nat :=
  (z180K18M4ProfileOneOrders ∪ {20}) ∪
    z180K18M4ProfileOneExtraOrders

/-- Complete set-side signature used by the second `m = 4` cover. -/
def z180K18M4RouteTwoOrders : Finset Nat :=
  z180K18M4ProfileTwoOrders ∪ {20}

/-- All possible nontrivial character orders in `ZMod 180`. -/
def z180NontrivialOrderSignature : Finset Nat :=
  {2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180}

/-- Complement for the profile `{3,9,20,60,180}`. -/
def z180K18M2ProfileOneComplement : Finset (ZMod 180) :=
  {0, 9, 18, 27, 36, 45, 54, 63, 72, 81}

/-- Complement for the profile `{3,4,9,12,36}`. -/
def z180K18M2ProfileTwoComplement : Finset (ZMod 180) :=
  {0, 9, 36, 45, 72, 81, 108, 117, 144, 153}

/-- Complement for the profile `{3,9,10,30,90}`. -/
def z180K18M4ProfileOneComplement : Finset (ZMod 180) :=
  {0, 9, 18, 27, 36, 90, 99, 108, 117, 126}

/-- Complement for the profile `{2,3,6,9,18}`. -/
def z180K18M4ProfileTwoComplement : Finset (ZMod 180) :=
  {17, 35, 53, 71, 89, 107, 125, 143, 161, 179}

/- Concrete representatives used by the four mask expansions.  Keeping
these as simp lemmas prevents the finite-set simplifier from leaving
`ZMod.val` matches in the polynomial exponents. -/
@[simp] private theorem z180_k18_cover_val_9 :
    (9 : ZMod 180).val = 9 := by decide
@[simp] private theorem z180_k18_cover_val_17 :
    (17 : ZMod 180).val = 17 := by decide
@[simp] private theorem z180_k18_cover_val_18 :
    (18 : ZMod 180).val = 18 := by decide
@[simp] private theorem z180_k18_cover_val_27 :
    (27 : ZMod 180).val = 27 := by decide
@[simp] private theorem z180_k18_cover_val_35 :
    (35 : ZMod 180).val = 35 := by decide
@[simp] private theorem z180_k18_cover_val_36 :
    (36 : ZMod 180).val = 36 := by decide
@[simp] private theorem z180_k18_cover_val_45 :
    (45 : ZMod 180).val = 45 := by decide
@[simp] private theorem z180_k18_cover_val_53 :
    (53 : ZMod 180).val = 53 := by decide
@[simp] private theorem z180_k18_cover_val_54 :
    (54 : ZMod 180).val = 54 := by decide
@[simp] private theorem z180_k18_cover_val_63 :
    (63 : ZMod 180).val = 63 := by decide
@[simp] private theorem z180_k18_cover_val_71 :
    (71 : ZMod 180).val = 71 := by decide
@[simp] private theorem z180_k18_cover_val_72 :
    (72 : ZMod 180).val = 72 := by decide
@[simp] private theorem z180_k18_cover_val_81 :
    (81 : ZMod 180).val = 81 := by decide
@[simp] private theorem z180_k18_cover_val_89 :
    (89 : ZMod 180).val = 89 := by decide
@[simp] private theorem z180_k18_cover_val_90 :
    (90 : ZMod 180).val = 90 := by decide
@[simp] private theorem z180_k18_cover_val_99 :
    (99 : ZMod 180).val = 99 := by decide
@[simp] private theorem z180_k18_cover_val_107 :
    (107 : ZMod 180).val = 107 := by decide
@[simp] private theorem z180_k18_cover_val_108 :
    (108 : ZMod 180).val = 108 := by decide
@[simp] private theorem z180_k18_cover_val_117 :
    (117 : ZMod 180).val = 117 := by decide
@[simp] private theorem z180_k18_cover_val_125 :
    (125 : ZMod 180).val = 125 := by decide
@[simp] private theorem z180_k18_cover_val_126 :
    (126 : ZMod 180).val = 126 := by decide
@[simp] private theorem z180_k18_cover_val_143 :
    (143 : ZMod 180).val = 143 := by decide
@[simp] private theorem z180_k18_cover_val_144 :
    (144 : ZMod 180).val = 144 := by decide
@[simp] private theorem z180_k18_cover_val_153 :
    (153 : ZMod 180).val = 153 := by decide
@[simp] private theorem z180_k18_cover_val_161 :
    (161 : ZMod 180).val = 161 := by decide
@[simp] private theorem z180_k18_cover_val_179 :
    (179 : ZMod 180).val = 179 := by decide

private noncomputable def z180K18Geom (step count : Nat) : Polynomial Int :=
  ∑ i ∈ Finset.range count, X ^ (step * i)

private theorem z180K18Geom_mul (step count : Nat) :
    z180K18Geom step count * (X ^ step - 1) =
      X ^ (step * count) - 1 := by
  simpa [z180K18Geom, pow_mul] using
    (geom_sum_mul (X ^ step : Polynomial Int) count)

/-- A cyclotomic factor indexed by a divisor of `step * count` which is not
already a divisor of `step` divides the corresponding geometric quotient.
This packages the exact algebra behind all four fixed complements. -/
private theorem cyclotomic_dvd_z180K18Geom
    (step count q : Nat) (hstep : 0 < step) (hcount : 0 < count)
    (hq : q ∈ (step * count).divisors \ step.divisors) :
    cyclotomic q Int ∣ z180K18Geom step count := by
  let P : Polynomial Int :=
    ∏ x ∈ (step * count).divisors \ step.divisors, cyclotomic x Int
  have hprod :
      (X ^ step - 1) * P = X ^ (step * count) - 1 := by
    exact X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
      Int ⟨count, rfl⟩ (Nat.mul_ne_zero hstep.ne' hcount.ne')
  have hfactor : (X ^ step - 1 : Polynomial Int) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero hstep (1 : Int)
  have hgeom : z180K18Geom step count = P := by
    apply mul_left_cancel₀ hfactor
    calc
      (X ^ step - 1) * z180K18Geom step count =
          z180K18Geom step count * (X ^ step - 1) := by ring
      _ = X ^ (step * count) - 1 := z180K18Geom_mul step count
      _ = (X ^ step - 1) * P := hprod.symm
  rw [hgeom]
  exact Finset.dvd_prod_of_mem (fun x ↦ cyclotomic x Int) hq

private theorem z180_mask_m2_profileOne_complement :
    maskPolynomial 180 z180K18M2ProfileOneComplement =
      z180K18Geom 9 10 := by
  simp +decide [maskPolynomial, z180K18M2ProfileOneComplement,
    z180K18Geom, Finset.sum_range_succ]
  ring

private theorem z180_mask_m2_profileTwo_complement :
    maskPolynomial 180 z180K18M2ProfileTwoComplement =
      z180K18Geom 9 2 * z180K18Geom 36 5 := by
  simp +decide [maskPolynomial, z180K18M2ProfileTwoComplement,
    z180K18Geom, Finset.sum_range_succ]
  ring

private theorem z180_mask_m4_profileOne_complement :
    maskPolynomial 180 z180K18M4ProfileOneComplement =
      z180K18Geom 90 2 * z180K18Geom 9 5 := by
  simp +decide [maskPolynomial, z180K18M4ProfileOneComplement,
    z180K18Geom, Finset.sum_range_succ]
  ring

private theorem z180_mask_m4_profileTwo_complement :
    maskPolynomial 180 z180K18M4ProfileTwoComplement =
      X ^ 17 * z180K18Geom 18 10 := by
  simp +decide [maskPolynomial, z180K18M4ProfileTwoComplement,
    z180K18Geom, Finset.sum_range_succ]
  ring

/-- Exact complement-side zero signature for the first `m = 2` route. -/
theorem z180_k18_m2_profileOne_complement_zeros :
    Z180K18OrderZerosOn z180K18M2ProfileOneComplement
      {2, 5, 6, 10, 15, 18, 30, 45, 90} := by
  intro q hq
  change cyclotomic q Int ∣
    maskPolynomial 180 z180K18M2ProfileOneComplement
  rw [z180_mask_m2_profileOne_complement]
  apply cyclotomic_dvd_z180K18Geom 9 10 q (by norm_num) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Exact complement-side zero signature for the second `m = 2` route. -/
theorem z180_k18_m2_profileTwo_complement_zeros :
    Z180K18OrderZerosOn z180K18M2ProfileTwoComplement
      {2, 5, 6, 10, 15, 18, 20, 30, 45, 60, 90, 180} := by
  intro q hq
  change cyclotomic q Int ∣
    maskPolynomial 180 z180K18M2ProfileTwoComplement
  rw [z180_mask_m2_profileTwo_complement]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 9 2 2 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 5 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 9 2 6 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 10 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 15 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 9 2 18 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 20 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 30 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 45 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 60 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 90 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 36 5 180 (by norm_num) (by norm_num) (by decide)) _

/-- Exact complement-side zero signature for the first `m = 4` route. -/
theorem z180_k18_m4_profileOne_complement_zeros :
    Z180K18OrderZerosOn z180K18M4ProfileOneComplement
      {4, 5, 12, 15, 20, 36, 45, 60, 180} := by
  intro q hq
  change cyclotomic q Int ∣
    maskPolynomial 180 z180K18M4ProfileOneComplement
  rw [z180_mask_m4_profileOne_complement]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 4 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 9 5 5 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 12 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 9 5 15 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 20 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 36 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_right
      (cyclotomic_dvd_z180K18Geom 9 5 45 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 60 (by norm_num) (by norm_num) (by decide)) _
  · exact dvd_mul_of_dvd_left
      (cyclotomic_dvd_z180K18Geom 90 2 180 (by norm_num) (by norm_num) (by decide)) _

/-- Exact complement-side zero signature for the second `m = 4` route. -/
theorem z180_k18_m4_profileTwo_complement_zeros :
    Z180K18OrderZerosOn z180K18M4ProfileTwoComplement
      {4, 5, 10, 12, 15, 20, 30, 36, 45, 60, 90, 180} := by
  intro q hq
  change cyclotomic q Int ∣
    maskPolynomial 180 z180K18M4ProfileTwoComplement
  rw [z180_mask_m4_profileTwo_complement]
  apply dvd_mul_of_dvd_right
  apply cyclotomic_dvd_z180K18Geom 18 10 q (by norm_num) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide

private theorem z180_frequencyOrder_mem_nontrivial
    {d : ZMod 180} (hd : d ≠ 0) :
    frequencyOrder 180 d ∈ z180NontrivialOrderSignature := by
  have hgt : 1 < frequencyOrder 180 d :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hd
  have hdvd : frequencyOrder 180 d ∣ 180 := frequencyOrder_dvd_modulus d
  have hmem : frequencyOrder 180 d ∈ (180 : Nat).divisors :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivisors :
      (180 : Nat).divisors = insert 1 z180NontrivialOrderSignature := by
    decide
  rw [hdivisors] at hmem
  simp only [Finset.mem_insert] at hmem
  rcases hmem with h | h
  · omega
  · exact h

/-- Generic order-signature version of the Fourier zero-cover theorem at
modulus 180. -/
theorem z180_tiles_of_orderZero_signatures
    (A B : Finset (ZMod 180)) (hcard : A.card * B.card = 180)
    {ordersA ordersB : Finset Nat}
    (hA : Z180K18OrderZerosOn A ordersA)
    (hB : Z180K18OrderZerosOn B ordersB)
    (hcover : ordersA ∪ ordersB = z180NontrivialOrderSignature) :
    Tiles A B := by
  apply tiles_of_cyclotomic_zero_cover A B hcard
  intro d hd
  have horder := z180_frequencyOrder_mem_nontrivial hd
  have hmem : frequencyOrder 180 d ∈ ordersA ∪ ordersB := by
    rw [hcover]
    exact horder
  rcases Finset.mem_union.mp hmem with hmemA | hmemB
  · exact Or.inl (by
      simpa [CyclotomicZero, Z180K18OrderZero] using
        hA (frequencyOrder 180 d) hmemA)
  · exact Or.inr (by
      simpa [CyclotomicZero, Z180K18OrderZero] using
        hB (frequencyOrder 180 d) hmemB)

/-- First `m = 2` Fourier-cover route. -/
theorem z180_k18_tiles_m2_profileOne
    {A : Finset (ZMod 180)} (hcard : A.card = 18)
    (hzeros : Z180K18OrderZerosOn A z180K18M2RouteOneOrders) :
    Tiles A z180K18M2ProfileOneComplement := by
  apply z180_tiles_of_orderZero_signatures A z180K18M2ProfileOneComplement
  · rw [hcard]
    decide
  · exact hzeros
  · exact z180_k18_m2_profileOne_complement_zeros
  · decide

/-- Second `m = 2` Fourier-cover route. -/
theorem z180_k18_tiles_m2_profileTwo
    {A : Finset (ZMod 180)} (hcard : A.card = 18)
    (hzeros : Z180K18OrderZerosOn A z180K18M2RouteTwoOrders) :
    Tiles A z180K18M2ProfileTwoComplement := by
  apply z180_tiles_of_orderZero_signatures A z180K18M2ProfileTwoComplement
  · rw [hcard]
    decide
  · exact hzeros
  · exact z180_k18_m2_profileTwo_complement_zeros
  · decide

/-- First `m = 4` Fourier-cover route. -/
theorem z180_k18_tiles_m4_profileOne
    {A : Finset (ZMod 180)} (hcard : A.card = 18)
    (hzeros : Z180K18OrderZerosOn A z180K18M4RouteOneOrders) :
    Tiles A z180K18M4ProfileOneComplement := by
  apply z180_tiles_of_orderZero_signatures A z180K18M4ProfileOneComplement
  · rw [hcard]
    decide
  · exact hzeros
  · exact z180_k18_m4_profileOne_complement_zeros
  · decide

/-- Second `m = 4` Fourier-cover route. -/
theorem z180_k18_tiles_m4_profileTwo
    {A : Finset (ZMod 180)} (hcard : A.card = 18)
    (hzeros : Z180K18OrderZerosOn A z180K18M4RouteTwoOrders) :
    Tiles A z180K18M4ProfileTwoComplement := by
  apply z180_tiles_of_orderZero_signatures A z180K18M4ProfileTwoComplement
  · rw [hcard]
    decide
  · exact hzeros
  · exact z180_k18_m4_profileTwo_complement_zeros
  · decide

#print axioms z180_k18_m2_profileOne_complement_zeros
#print axioms z180_k18_m2_profileTwo_complement_zeros
#print axioms z180_k18_m4_profileOne_complement_zeros
#print axioms z180_k18_m4_profileTwo_complement_zeros
#print axioms z180_k18_tiles_m2_profileOne
#print axioms z180_k18_tiles_m2_profileTwo
#print axioms z180_k18_tiles_m4_profileOne
#print axioms z180_k18_tiles_m4_profileTwo

end Fuglede
