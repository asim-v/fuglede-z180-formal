import Fuglede.Z180K10Structural
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Characteristic-three descent through the projection modulo twenty

For `3 ∤ m`, the three possible indices `m`, `3m`, and `9m` all contain
`Phi_m` after reduction to `F_3`.  This file also proves that reducing every
mask exponent modulo twenty preserves divisibility by `Phi_m` when `m ∣ 20`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Direct characteristic-three reduction of an integer cyclotomic divisor. -/
theorem cyclotomic_mod_three_dvd_of_index_dvd
    {m : Nat} {P : Polynomial Int}
    (hdiv : cyclotomic m Int ∣ P) :
    cyclotomic m (ZMod 3) ∣ P.map (Int.castRingHom (ZMod 3)) := by
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 3)) hdiv
  rw [map_cyclotomic] at hmap
  exact hmap

/-- The `3m` case of characteristic-three cyclotomic reduction. -/
theorem cyclotomic_mod_three_dvd_of_three_mul_index_dvd
    {m : Nat} (hm : ¬ 3 ∣ m) {P : Polynomial Int}
    (hdiv : cyclotomic (3 * m) Int ∣ P) :
    cyclotomic m (ZMod 3) ∣ P.map (Int.castRingHom (ZMod 3)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 3)) hdiv
  rw [map_cyclotomic] at hmap
  have hpow :
      cyclotomic (3 * m) (ZMod 3) =
        cyclotomic m (ZMod 3) ^ 2 := by
    simpa using
      (cyclotomic_mul_prime_pow_eq (ZMod 3) hm
        (k := 1) (by norm_num))
  rw [hpow] at hmap
  exact (dvd_pow_self (cyclotomic m (ZMod 3)) (by norm_num)).trans hmap

/-- The `9m` case of characteristic-three cyclotomic reduction. -/
theorem cyclotomic_mod_three_dvd_of_nine_mul_index_dvd
    {m : Nat} (hm : ¬ 3 ∣ m) {P : Polynomial Int}
    (hdiv : cyclotomic (9 * m) Int ∣ P) :
    cyclotomic m (ZMod 3) ∣ P.map (Int.castRingHom (ZMod 3)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 3)) hdiv
  rw [map_cyclotomic] at hmap
  have hpow :
      cyclotomic (9 * m) (ZMod 3) =
        cyclotomic m (ZMod 3) ^ 6 := by
    simpa using
      (cyclotomic_mul_prime_pow_eq (ZMod 3) hm
        (k := 2) (by norm_num))
  rw [hpow] at hmap
  exact (dvd_pow_self (cyclotomic m (ZMod 3)) (by norm_num)).trans hmap

/-- Uniform characteristic-three bridge for the three possible lifts of an
order coprime to three. -/
theorem cyclotomic_mod_three_dvd_of_index_cases
    {m q : Nat} (hm : ¬ 3 ∣ m) {P : Polynomial Int}
    (hq : q = m ∨ q = 3 * m ∨ q = 9 * m)
    (hdiv : cyclotomic q Int ∣ P) :
    cyclotomic m (ZMod 3) ∣ P.map (Int.castRingHom (ZMod 3)) := by
  rcases hq with rfl | rfl | rfl
  · exact cyclotomic_mod_three_dvd_of_index_dvd hdiv
  · exact cyclotomic_mod_three_dvd_of_three_mul_index_dvd hm hdiv
  · exact cyclotomic_mod_three_dvd_of_nine_mul_index_dvd hm hdiv

/-- A representative modulo twenty, packaged as a bounded exponent. -/
noncomputable def z180Projection20Coordinate (x : ZMod 180) : Fin 20 :=
  Fin.mk (z180K10Projection20 x).val (z180K10Projection20 x).val_lt

/-- Number of elements in a prescribed projection fibre. -/
noncomputable def z180Projection20Occupancy
    (S : Finset (ZMod 180)) (i : Fin 20) : Nat :=
  (S.filter fun x => z180Projection20Coordinate x = i).card

/-- Projected mask over `F_3`. -/
noncomputable def z180Projection20MaskModThree
    (S : Finset (ZMod 180)) : Polynomial (ZMod 3) :=
  S.sum fun x => monomial (z180Projection20Coordinate x).val 1

theorem z180Projection20Coordinate_val (x : ZMod 180) :
    (z180Projection20Coordinate x).val = x.val % 20 := by
  change (ZMod.cast x : ZMod 20).val = x.val % 20
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

theorem z180Projection20Coordinate_eq_iff_projection_eq
    (x y : ZMod 180) :
    z180Projection20Coordinate x = z180Projection20Coordinate y ↔
      z180K10Projection20 x = z180K10Projection20 y := by
  constructor
  · intro h
    apply ZMod.val_injective
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    exact congrArg ZMod.val h

/-- Coefficients of the projected mask are occupancies reduced modulo three. -/
theorem coeff_z180Projection20MaskModThree
    (S : Finset (ZMod 180)) (i : Fin 20) :
    (z180Projection20MaskModThree S).coeff i.val =
      (z180Projection20Occupancy S i : ZMod 3) := by
  classical
  simp only [z180Projection20MaskModThree, finsetSum_coeff,
    coeff_monomial]
  rw [z180Projection20Occupancy, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxi : z180Projection20Coordinate x = i
  · simp [hxi]
  · have hv : ¬ (z180Projection20Coordinate x).val = i.val :=
      fun h => hxi (Fin.ext h)
    simp [hxi, hv]

/-- The projected mask has degree strictly below twenty. -/
theorem degree_z180Projection20MaskModThree_lt
    (S : Finset (ZMod 180)) :
    (z180Projection20MaskModThree S).degree < (20 : Nat) := by
  apply (degree_lt_iff_coeff_zero
    (z180Projection20MaskModThree S) 20).2
  intro m hm
  have hmNat : 20 ≤ m := by exact_mod_cast hm
  simp only [z180Projection20MaskModThree, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : ¬ (z180Projection20Coordinate x).val = m := by
    have hlt := (z180Projection20Coordinate x).isLt
    omega
  rw [coeff_monomial, if_neg hne]

/-- The twenty projection fibres partition the original set. -/
theorem sum_z180Projection20Occupancy (S : Finset (ZMod 180)) :
    (∑ i : Fin 20, z180Projection20Occupancy S i) = S.card := by
  classical
  simpa [z180Projection20Occupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter S
      (Finset.univ : Finset (Fin 20)) z180Projection20Coordinate)

/-- Injectivity modulo twenty makes each projected occupancy zero or one. -/
theorem z180Projection20Occupancy_le_one_of_injOn
    {S : Finset (ZMod 180)}
    (hinj : Set.InjOn z180K10Projection20 (S : Set (ZMod 180)))
    (i : Fin 20) :
    z180Projection20Occupancy S i ≤ 1 := by
  classical
  rw [z180Projection20Occupancy]
  apply Finset.card_le_one_iff.mpr
  intro x y hx hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  apply hinj hx'.1 hy'.1
  exact (z180Projection20Coordinate_eq_iff_projection_eq x y).mp
    (hx'.2.trans hy'.2.symm)

/-- Evaluating the projected mask at one recovers the set cardinality in
the coefficient field. -/
theorem eval_one_z180Projection20MaskModThree
    (S : Finset (ZMod 180)) :
    (z180Projection20MaskModThree S).eval 1 = (S.card : ZMod 3) := by
  classical
  simp [z180Projection20MaskModThree, Polynomial.eval_finsetSum]

private theorem map_maskPolynomial_mod_three_eq_sum
    (S : Finset (ZMod 180)) :
    (maskPolynomial 180 S).map (Int.castRingHom (ZMod 3)) =
      S.sum (fun x => monomial x.val 1) := by
  classical
  rw [maskPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [monomial_one_right_eq_X_pow]

/-- One exponent and its residue modulo twenty differ by a multiple of
`X^20 - 1`. -/
private theorem X_pow_sub_projection20_dvd (x : ZMod 180) :
    (X ^ 20 - 1 : Polynomial (ZMod 3)) ∣
      monomial x.val 1 -
        monomial (z180Projection20Coordinate x).val 1 := by
  rw [monomial_one_right_eq_X_pow, monomial_one_right_eq_X_pow]
  rw [z180Projection20Coordinate_val]
  let q := x.val / 20
  have hmultiple : 20 ∣ 20 * q := dvd_mul_right 20 q
  have hbase : (X ^ 20 - 1 : Polynomial (ZMod 3)) ∣
      X ^ (20 * q) - 1 := dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ 20 - 1 : Polynomial (ZMod 3)) ∣
      X ^ (x.val % 20) * (X ^ (20 * q) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : x.val % 20 + 20 * q = x.val := by
    simpa [q] using Nat.mod_add_div x.val 20
  have hpow : X ^ x.val =
      (X : Polynomial (ZMod 3)) ^ (x.val % 20) * X ^ (20 * q) := by
    calc
      X ^ x.val = X ^ (x.val % 20 + 20 * q) := by rw [hn]
      _ = _ := pow_add _ _ _
  rw [hpow]
  simpa [mul_sub] using hmul

/-- The mapped integer mask and its exponent projection are congruent modulo
`X^20 - 1`. -/
theorem X_pow_20_sub_one_dvd_mask_map_sub_projection
    (S : Finset (ZMod 180)) :
    (X ^ 20 - 1 : Polynomial (ZMod 3)) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 3)) -
        z180Projection20MaskModThree S := by
  classical
  rw [map_maskPolynomial_mod_three_eq_sum,
    z180Projection20MaskModThree]
  have hs : (X ^ 20 - 1 : Polynomial (ZMod 3)) ∣
      S.sum (fun x => monomial x.val 1 -
        monomial (z180Projection20Coordinate x).val 1) := by
    apply Finset.dvd_sum
    intro x hx
    exact X_pow_sub_projection20_dvd x
  simpa [Finset.sum_sub_distrib] using hs

/-- A factor `Phi_m`, with `m ∣ 20`, survives exponent projection modulo
twenty. -/
theorem cyclotomic_dvd_projection20MaskModThree_of_dvd_mapped_mask
    {m : Nat} (hm20 : m ∣ 20) {S : Finset (ZMod 180)}
    (hdiv : cyclotomic m (ZMod 3) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 3))) :
    cyclotomic m (ZMod 3) ∣ z180Projection20MaskModThree S := by
  have hcycloMod : cyclotomic m (ZMod 3) ∣
      (X ^ 20 - 1 : Polynomial (ZMod 3)) :=
    (cyclotomic.dvd_X_pow_sub_one m (ZMod 3)).trans
      (dvd_pow_sub_one_of_dvd hm20)
  have hdiff : cyclotomic m (ZMod 3) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 3)) -
        z180Projection20MaskModThree S :=
    hcycloMod.trans (X_pow_20_sub_one_dvd_mask_map_sub_projection S)
  have hsub := dvd_sub hdiv hdiff
  simpa using hsub

/-- Full typed descent for an index equal to `m`, `3m`, or `9m`. -/
theorem cyclotomic_dvd_projection20MaskModThree_of_index_cases_dvd_mask
    {m q : Nat} (hm : ¬ 3 ∣ m) (hm20 : m ∣ 20)
    {S : Finset (ZMod 180)}
    (hq : q = m ∨ q = 3 * m ∨ q = 9 * m)
    (hdiv : cyclotomic q Int ∣ maskPolynomial 180 S) :
    cyclotomic m (ZMod 3) ∣ z180Projection20MaskModThree S := by
  apply cyclotomic_dvd_projection20MaskModThree_of_dvd_mapped_mask hm20
  exact cyclotomic_mod_three_dvd_of_index_cases hm hq hdiv

#print axioms cyclotomic_mod_three_dvd_of_index_cases
#print axioms cyclotomic_dvd_projection20MaskModThree_of_index_cases_dvd_mask

end Fuglede
