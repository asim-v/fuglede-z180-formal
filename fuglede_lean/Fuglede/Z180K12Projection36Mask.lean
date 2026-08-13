import Fuglede.CyclicCertificate
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# The integral projection of a `ZMod 180` mask to exponents modulo 36

This is the polynomial bridge used by the cardinality-twelve sieve.  It is
deliberately independent of the finite Presburger certificates: those consume
the thirty-six occupancies exposed here.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- A representative of the projection modulo 36, packaged with its bound. -/
noncomputable def z180Projection36Coordinate (x : ZMod 180) : Fin 36 :=
  Fin.mk (ZMod.cast x : ZMod 36).val
    (ZMod.cast x : ZMod 36).val_lt

/-- Number of points in a prescribed projection fibre. -/
noncomputable def z180Projection36Occupancy
    (S : Finset (ZMod 180)) (i : Fin 36) : Nat :=
  (S.filter fun x => z180Projection36Coordinate x = i).card

/-- Integral mask after reducing every exponent modulo 36. -/
noncomputable def z180Projection36Mask
    (S : Finset (ZMod 180)) : Polynomial Int :=
  S.sum fun x => monomial (z180Projection36Coordinate x).val 1

theorem z180Projection36Coordinate_val (x : ZMod 180) :
    (z180Projection36Coordinate x).val = x.val % 36 := by
  change (ZMod.cast x : ZMod 36).val = x.val % 36
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

theorem z180Projection36Coordinate_eq_iff_cast_eq
    (x y : ZMod 180) :
    z180Projection36Coordinate x = z180Projection36Coordinate y ↔
      (ZMod.cast x : ZMod 36) = ZMod.cast y := by
  constructor
  · intro h
    apply ZMod.val_injective
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    exact congrArg ZMod.val h

/-- Coefficients of the projected mask are the projection occupancies. -/
theorem coeff_z180Projection36Mask
    (S : Finset (ZMod 180)) (i : Fin 36) :
    (z180Projection36Mask S).coeff i.val =
      (z180Projection36Occupancy S i : Int) := by
  classical
  simp only [z180Projection36Mask, finsetSum_coeff, coeff_monomial]
  rw [z180Projection36Occupancy, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxi : z180Projection36Coordinate x = i
  · simp [hxi]
  · have hv : ¬ (z180Projection36Coordinate x).val = i.val :=
      fun h => hxi (Fin.ext h)
    simp [hxi, hv]

/-- The projected mask has degree strictly below 36. -/
theorem degree_z180Projection36Mask_lt
    (S : Finset (ZMod 180)) :
    (z180Projection36Mask S).degree < (36 : Nat) := by
  apply (degree_lt_iff_coeff_zero (z180Projection36Mask S) 36).2
  intro m hm
  have hmNat : 36 ≤ m := by exact_mod_cast hm
  simp only [z180Projection36Mask, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : ¬ (z180Projection36Coordinate x).val = m := by
    have hlt : (z180Projection36Coordinate x).val < 36 :=
      (z180Projection36Coordinate x).isLt
    omega
  rw [coeff_monomial, if_neg hne]

/-- The thirty-six projection fibres partition the original set. -/
theorem sum_z180Projection36Occupancy (S : Finset (ZMod 180)) :
    (∑ i : Fin 36, z180Projection36Occupancy S i) = S.card := by
  classical
  simpa [z180Projection36Occupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter S
      (Finset.univ : Finset (Fin 36)) z180Projection36Coordinate)

private theorem sum_projection36_fibre_monomial
    (S : Finset (ZMod 180)) (i : Fin 36) :
    ∑ x ∈ S.filter (fun x => z180Projection36Coordinate x = i),
        monomial (z180Projection36Coordinate x).val (1 : Int) =
      monomial i.val (z180Projection36Occupancy S i : Int) := by
  classical
  calc
    (∑ x ∈ S.filter (fun x => z180Projection36Coordinate x = i),
        monomial (z180Projection36Coordinate x).val (1 : Int)) =
        ∑ _x ∈ S.filter (fun x => z180Projection36Coordinate x = i),
          monomial i.val (1 : Int) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = monomial i.val (z180Projection36Occupancy S i : Int) := by
      ext j
      by_cases hij : i.val = j
      · simp [hij, z180Projection36Occupancy]
      · simp [coeff_monomial, hij]

/-- Fibrewise form of the projected mask, convenient for concrete remainder
normalization. -/
theorem z180Projection36Mask_eq_sum_occupancy
    (S : Finset (ZMod 180)) :
    z180Projection36Mask S =
      ∑ i : Fin 36,
        monomial i.val (z180Projection36Occupancy S i : Int) := by
  classical
  let f : ZMod 180 → Polynomial Int := fun x =>
    monomial (z180Projection36Coordinate x).val 1
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    S (Finset.univ : Finset (Fin 36)) z180Projection36Coordinate f
  have hfilter :
      S.filter (fun x => z180Projection36Coordinate x ∈
        (Finset.univ : Finset (Fin 36))) = S := by
    simp
  rw [hfilter] at hfiber
  rw [z180Projection36Mask]
  calc
    S.sum f =
        ∑ i : Fin 36,
          ∑ x ∈ S.filter (fun x => z180Projection36Coordinate x = i),
            f x := by simpa using hfiber.symm
    _ = ∑ i : Fin 36,
        monomial i.val (z180Projection36Occupancy S i : Int) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_projection36_fibre_monomial S i

/-- Injectivity modulo 36 makes every occupancy a zero-one variable. -/
theorem z180Projection36Occupancy_le_one_of_injOn
    {S : Finset (ZMod 180)}
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (S : Set (ZMod 180))) (i : Fin 36) :
    z180Projection36Occupancy S i ≤ 1 := by
  classical
  rw [z180Projection36Occupancy]
  apply Finset.card_le_one_iff.mpr
  intro x y hx hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  apply hinj hx'.1 hy'.1
  exact (z180Projection36Coordinate_eq_iff_cast_eq x y).mp
    (hx'.2.trans hy'.2.symm)

private theorem maskPolynomial_eq_sum_monomial
    (S : Finset (ZMod 180)) :
    maskPolynomial 180 S = S.sum (fun x => monomial x.val 1) := by
  classical
  rw [maskPolynomial]
  apply Finset.sum_congr rfl
  intro x hx
  simp [monomial_one_right_eq_X_pow]

/-- One exponent and its reduction modulo 36 differ by a multiple of
`X^36 - 1`. -/
private theorem X_pow_sub_projection36_dvd (x : ZMod 180) :
    (X ^ 36 - 1 : Polynomial Int) ∣
      monomial x.val 1 -
        monomial (z180Projection36Coordinate x).val 1 := by
  rw [monomial_one_right_eq_X_pow, monomial_one_right_eq_X_pow]
  rw [z180Projection36Coordinate_val]
  let q := x.val / 36
  have hmultiple : 36 ∣ 36 * q := dvd_mul_right 36 q
  have hbase : (X ^ 36 - 1 : Polynomial Int) ∣
      X ^ (36 * q) - 1 := dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ 36 - 1 : Polynomial Int) ∣
      X ^ (x.val % 36) * (X ^ (36 * q) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : x.val % 36 + 36 * q = x.val := by
    simpa [q] using Nat.mod_add_div x.val 36
  have hpow : X ^ x.val =
      (X : Polynomial Int) ^ (x.val % 36) * X ^ (36 * q) := by
    calc
      X ^ x.val = X ^ (x.val % 36 + 36 * q) := by rw [hn]
      _ = _ := pow_add _ _ _
  rw [hpow]
  simpa [mul_sub] using hmul

/-- The original and projected integral masks are congruent modulo
`X^36 - 1`. -/
theorem X_pow_36_sub_one_dvd_mask_sub_projection
    (S : Finset (ZMod 180)) :
    (X ^ 36 - 1 : Polynomial Int) ∣
      maskPolynomial 180 S - z180Projection36Mask S := by
  classical
  rw [maskPolynomial_eq_sum_monomial, z180Projection36Mask]
  have hs : (X ^ 36 - 1 : Polynomial Int) ∣
      S.sum (fun x => monomial x.val 1 -
        monomial (z180Projection36Coordinate x).val 1) := by
    apply Finset.dvd_sum
    intro x hx
    exact X_pow_sub_projection36_dvd x
  simpa [Finset.sum_sub_distrib] using hs

/-- For every `m | 36`, cyclotomic divisibility is unchanged by the exponent
projection modulo 36. -/
theorem cyclotomic_dvd_projection36Mask_iff_dvd_mask
    {m : Nat} (hm36 : m ∣ 36) {S : Finset (ZMod 180)} :
    cyclotomic m Int ∣ z180Projection36Mask S ↔
      cyclotomic m Int ∣ maskPolynomial 180 S := by
  have hcycloMod : cyclotomic m Int ∣
      (X ^ 36 - 1 : Polynomial Int) :=
    (cyclotomic.dvd_X_pow_sub_one m Int).trans
      (dvd_pow_sub_one_of_dvd hm36)
  have hdiff : cyclotomic m Int ∣
      maskPolynomial 180 S - z180Projection36Mask S :=
    hcycloMod.trans (X_pow_36_sub_one_dvd_mask_sub_projection S)
  constructor
  · intro hprojected
    have hadd := dvd_add hdiff hprojected
    simpa using hadd
  · intro hmask
    have hsub := dvd_sub hmask hdiff
    simpa using hsub

/-- Characteristic-five reduction of the coprime `Phi_(5m)` relation. -/
theorem cyclotomic_mod_five_dvd_of_five_mul_index_dvd
    {m : Nat} (hm : ¬ 5 ∣ m) {P : Polynomial Int}
    (hdiv : cyclotomic (5 * m) Int ∣ P) :
    cyclotomic m (ZMod 5) ∣ P.map (Int.castRingHom (ZMod 5)) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 5)) hdiv
  rw [map_cyclotomic] at hmap
  rw [mul_comm,
    cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod 5) hm] at hmap
  exact (dvd_pow_self (cyclotomic m (ZMod 5)) (by norm_num)).trans hmap

/-- A `Phi_30` divisor makes the projected mask divisible by `Phi_6` after
reducing coefficients modulo five. -/
theorem cyclotomic_six_mod_five_dvd_projection36Mask_of_phi30_dvd_mask
    {S : Finset (ZMod 180)}
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 S) :
    cyclotomic 6 (ZMod 5) ∣
      (z180Projection36Mask S).map (Int.castRingHom (ZMod 5)) := by
  have hmapped : cyclotomic 6 (ZMod 5) ∣
      (maskPolynomial 180 S).map (Int.castRingHom (ZMod 5)) := by
    apply cyclotomic_mod_five_dvd_of_five_mul_index_dvd (m := 6)
    · norm_num
    · simpa using h30
  have hraw := Polynomial.map_dvd (Int.castRingHom (ZMod 5))
    (X_pow_36_sub_one_dvd_mask_sub_projection S)
  have hdiffMapped :
      (X ^ 36 - 1 : Polynomial (ZMod 5)) ∣
        (maskPolynomial 180 S).map (Int.castRingHom (ZMod 5)) -
          (z180Projection36Mask S).map (Int.castRingHom (ZMod 5)) := by
    simpa using hraw
  have hcyclo : cyclotomic 6 (ZMod 5) ∣
      (X ^ 36 - 1 : Polynomial (ZMod 5)) :=
    (cyclotomic.dvd_X_pow_sub_one 6 (ZMod 5)).trans
      (dvd_pow_sub_one_of_dvd (by norm_num : 6 ∣ 36))
  have hdiff := hcyclo.trans hdiffMapped
  have hsub := dvd_sub hmapped hdiff
  simpa using hsub

#print axioms coeff_z180Projection36Mask
#print axioms z180Projection36Mask_eq_sum_occupancy
#print axioms z180Projection36Occupancy_le_one_of_injOn
#print axioms cyclotomic_dvd_projection36Mask_iff_dvd_mask
#print axioms cyclotomic_six_mod_five_dvd_projection36Mask_of_phi30_dvd_mask

end Fuglede
