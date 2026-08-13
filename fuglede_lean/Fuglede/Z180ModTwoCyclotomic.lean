import Fuglede.Z180K15Structural
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# The characteristic-two projection used in the `|S| = 15` descent

This file formalizes the algebraic content of FKMS Lemma 2.3 for the
specialization

`ZMod 180 -> ZMod 45`, with omitted prime `2`.

An integer divisibility by `Phi_(2m)` reduces to a divisibility by `Phi_m`
over `ZMod 2`.  Reducing every exponent modulo 45 does not change that
divisibility when `m | 45`.  The latter assertion is proved at polynomial
level: the original and projected masks differ by a multiple of
`X^45 - 1`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Characteristic-two reduction of the `p = 2`, `k = 1` case of FKMS
Lemma 2.3. -/
theorem cyclotomic_mod_two_dvd_of_twice_index_dvd
    {m : Nat} (hm : ¬ 2 ∣ m) {P : Polynomial Int}
    (hdiv : cyclotomic (2 * m) Int ∣ P) :
    cyclotomic m (ZMod 2) ∣ P.map (Int.castRingHom (ZMod 2)) := by
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 2)) hdiv
  rw [map_cyclotomic] at hmap
  rw [mul_comm,
    cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod 2) hm] at hmap
  simpa using hmap

/-- A representative modulo 45, packaged as a bounded exponent. -/
noncomputable def z180Projection45Coordinate (x : ZMod 180) : Fin 45 :=
  Fin.mk (ZMod.cast x : ZMod 45).val
    (ZMod.cast x : ZMod 45).val_lt

/-- Number of elements of `S` in a prescribed fiber of the projection to
`ZMod 45`. -/
noncomputable def z180Projection45Occupancy
    (S : Finset (ZMod 180)) (i : Fin 45) : Nat :=
  (S.filter fun x => z180Projection45Coordinate x = i).card

/-- The projected mask over `F_2`; repeated residues contribute with their
multiplicity modulo two. -/
noncomputable def z180Projection45MaskModTwo
    (S : Finset (ZMod 180)) : Polynomial (ZMod 2) :=
  S.sum fun x => monomial (z180Projection45Coordinate x).val 1

theorem z180Projection45Coordinate_val (x : ZMod 180) :
    (z180Projection45Coordinate x).val = x.val % 45 := by
  change (ZMod.cast x : ZMod 45).val = x.val % 45
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

/-- The coefficient of the projected mask is the parity of the
corresponding fiber occupancy. -/
theorem coeff_z180Projection45MaskModTwo
    (S : Finset (ZMod 180)) (i : Fin 45) :
    (z180Projection45MaskModTwo S).coeff i.val =
      (z180Projection45Occupancy S i : ZMod 2) := by
  classical
  simp only [z180Projection45MaskModTwo, finsetSum_coeff,
    coeff_monomial]
  rw [z180Projection45Occupancy, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxi : z180Projection45Coordinate x = i
  · simp [hxi]
  · have hv : ¬ (z180Projection45Coordinate x).val = i.val :=
      fun h => hxi (Fin.ext h)
    simp [hxi, hv]

/-- The projected mask has degree strictly below 45. -/
theorem degree_z180Projection45MaskModTwo_lt
    (S : Finset (ZMod 180)) :
    (z180Projection45MaskModTwo S).degree < (45 : Nat) := by
  apply (degree_lt_iff_coeff_zero (z180Projection45MaskModTwo S) 45).2
  intro m hm
  have hmNat : 45 ≤ m := by exact_mod_cast hm
  simp only [z180Projection45MaskModTwo, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : ¬ (z180Projection45Coordinate x).val = m := by
    have hlt : (z180Projection45Coordinate x).val < 45 :=
      (z180Projection45Coordinate x).isLt
    omega
  rw [coeff_monomial, if_neg hne]

/-- The 45 projection fibers partition the set. -/
theorem sum_z180Projection45Occupancy (S : Finset (ZMod 180)) :
    (∑ i : Fin 45, z180Projection45Occupancy S i) = S.card := by
  classical
  simpa [z180Projection45Occupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter S
      (Finset.univ : Finset (Fin 45)) z180Projection45Coordinate)

private theorem map_maskPolynomial_mod_two_eq_sum
    (S : Finset (ZMod 180)) :
    (maskPolynomial 180 S).map (Int.castRingHom (ZMod 2)) =
      S.sum (fun x => monomial x.val 1) := by
  classical
  rw [maskPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [monomial_one_right_eq_X_pow]

/-- A single exponent and its reduction modulo 45 differ by a multiple of
`X^45 - 1`. -/
private theorem X_pow_sub_projection45_dvd (x : ZMod 180) :
    (X ^ 45 - 1 : Polynomial (ZMod 2)) ∣
      monomial x.val 1 -
        monomial (z180Projection45Coordinate x).val 1 := by
  rw [monomial_one_right_eq_X_pow, monomial_one_right_eq_X_pow]
  rw [z180Projection45Coordinate_val]
  let q := x.val / 45
  have hmultiple : 45 ∣ 45 * q := dvd_mul_right 45 q
  have hbase : (X ^ 45 - 1 : Polynomial (ZMod 2)) ∣
      X ^ (45 * q) - 1 := dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ 45 - 1 : Polynomial (ZMod 2)) ∣
      X ^ (x.val % 45) * (X ^ (45 * q) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : x.val % 45 + 45 * q = x.val := by
    simpa [q] using Nat.mod_add_div x.val 45
  have hpow : X ^ x.val =
      (X : Polynomial (ZMod 2)) ^ (x.val % 45) * X ^ (45 * q) := by
    calc
      X ^ x.val = X ^ (x.val % 45 + 45 * q) := by rw [hn]
      _ = _ := pow_add _ _ _
  rw [hpow]
  simpa [mul_sub] using hmul

/-- The characteristic-two mask and its projection modulo 45 are congruent
modulo `X^45 - 1`. -/
theorem X_pow_45_sub_one_dvd_mask_map_sub_projection
    (S : Finset (ZMod 180)) :
    (X ^ 45 - 1 : Polynomial (ZMod 2)) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 2)) -
        z180Projection45MaskModTwo S := by
  classical
  rw [map_maskPolynomial_mod_two_eq_sum, z180Projection45MaskModTwo]
  have hs : (X ^ 45 - 1 : Polynomial (ZMod 2)) ∣
      S.sum (fun x => monomial x.val 1 -
        monomial (z180Projection45Coordinate x).val 1) := by
    apply Finset.dvd_sum
    intro x hx
    exact X_pow_sub_projection45_dvd x
  simpa [Finset.sum_sub_distrib] using hs

/-- Divisibility by `Phi_m`, for `m | 45`, survives exponent projection
modulo 45. -/
theorem cyclotomic_dvd_projection45MaskModTwo_of_dvd_mapped_mask
    {m : Nat} (hm45 : m ∣ 45) {S : Finset (ZMod 180)}
    (hdiv : cyclotomic m (ZMod 2) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 2))) :
    cyclotomic m (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  have hcycloMod : cyclotomic m (ZMod 2) ∣
      (X ^ 45 - 1 : Polynomial (ZMod 2)) :=
    (cyclotomic.dvd_X_pow_sub_one m (ZMod 2)).trans
      (dvd_pow_sub_one_of_dvd hm45)
  have hdiff : cyclotomic m (ZMod 2) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 2)) -
        z180Projection45MaskModTwo S :=
    hcycloMod.trans (X_pow_45_sub_one_dvd_mask_map_sub_projection S)
  have hsub := dvd_sub hdiv hdiff
  simpa using hsub

/-- Typed FKMS Lemma 2.3 followed by the exact projection bridge. -/
theorem cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
    {m : Nat} (hm : ¬ 2 ∣ m) (hm45 : m ∣ 45)
    {S : Finset (ZMod 180)}
    (hdiv : cyclotomic (2 * m) Int ∣ maskPolynomial 180 S) :
    cyclotomic m (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mapped_mask hm45
  exact cyclotomic_mod_two_dvd_of_twice_index_dvd hm hdiv

#print axioms cyclotomic_mod_two_dvd_of_twice_index_dvd
#print axioms cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask

end Fuglede
