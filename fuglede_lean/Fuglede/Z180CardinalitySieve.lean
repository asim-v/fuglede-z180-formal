import Fuglede.Z180Projection
import Fuglede.Z180ProjectionTiles
import Mathlib.Tactic.IntervalCases

/-!
# Elementary cardinality sieve at modulus 180

Projection to the complementary factor is injective whenever the relevant
prime does not divide the spectral cardinality.  The three resulting bounds
reduce all cardinalities at most `90` to divisors of `180` plus twelve exact
exceptions.  This is a kernel-checked arithmetic reduction; it does not by
itself exclude those exceptions.
-/

namespace Fuglede

/-- If three does not divide the common spectral cardinality, reduction
modulo twenty is injective. -/
theorem z180_projection20_injOn_of_spectral_not_three_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hnot : ¬ 3 ∣ A.card) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 20))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  have hdivL : 3 ∣ L.card := by
    rcases z180_frequencyOrder_three_or_nine_of_cast20_eq x y hxy hcast with
      hthree | hnine
    · exact prime_dvd_card_of_cyclotomicZero
        (by norm_num) L (x - y) hthree hzero
    · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
        (p := 3) (N := 180) (by norm_num) 1 L
      simpa [CyclotomicZero, hnine] using hzero
  apply hnot
  simpa [hSpec.2.1] using hdivL

/-- If two does not divide the common spectral cardinality, reduction modulo
forty-five is injective. -/
theorem z180_projection45_injOn_of_spectral_not_two_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hnot : ¬ 2 ∣ A.card) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 45))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  have hdivL : 2 ∣ L.card := by
    rcases z180_frequencyOrder_two_or_four_of_cast45_eq x y hxy hcast with
      htwo | hfour
    · exact prime_dvd_card_of_cyclotomicZero
        (by norm_num) L (x - y) htwo hzero
    · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
        (p := 2) (N := 180) (by norm_num) 1 L
      simpa [CyclotomicZero, hfour] using hzero
  apply hnot
  simpa [hSpec.2.1] using hdivL

theorem z180_card_le_twenty_of_spectral_not_three_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hnot : ¬ 3 ∣ A.card) :
    A.card ≤ 20 := by
  have hinj := z180_projection20_injOn_of_spectral_not_three_dvd hSpec hnot
  simpa using
    (Finset.card_le_card_of_injOn
      (fun x : ZMod 180 => (ZMod.cast x : ZMod 20))
      (s := A) (t := (Finset.univ : Finset (ZMod 20)))
      (fun _ _ => Finset.mem_univ _) hinj)

theorem z180_card_le_forty_five_of_spectral_not_two_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hnot : ¬ 2 ∣ A.card) :
    A.card ≤ 45 := by
  have hinj := z180_projection45_injOn_of_spectral_not_two_dvd hSpec hnot
  simpa using
    (Finset.card_le_card_of_injOn
      (fun x : ZMod 180 => (ZMod.cast x : ZMod 45))
      (s := A) (t := (Finset.univ : Finset (ZMod 45)))
      (fun _ _ => Finset.mem_univ _) hinj)

theorem z180_card_le_thirty_six_of_spectral_not_five_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hnot : ¬ 5 ∣ A.card) :
    A.card ≤ 36 := by
  have hinj := z180_projection36_injOn_of_spectral_not_five_dvd hSpec hnot
  simpa using
    (Finset.card_le_card_of_injOn
      (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (s := A) (t := (Finset.univ : Finset (ZMod 36)))
      (fun _ _ => Finset.mem_univ _) hinj)

/-- Pure arithmetic form of the three projection bounds. -/
theorem z180_cardinality_arithmetic_sieve (k : Nat)
    (hpos : 0 < k) (hle : k ≤ 90)
    (h2 : ¬ 2 ∣ k → k ≤ 45)
    (h3 : ¬ 3 ∣ k → k ≤ 20)
    (h5 : ¬ 5 ∣ k → k ≤ 36) :
    k ∣ 180 ∨
      k = 7 ∨ k = 8 ∨ k = 11 ∨ k = 13 ∨ k = 14 ∨ k = 16 ∨
      k = 17 ∨ k = 19 ∨ k = 21 ∨ k = 24 ∨ k = 27 ∨ k = 33 := by
  interval_cases k <;>
    (try norm_num at h2) <;>
    (try norm_num at h3) <;>
    (try norm_num at h5) <;>
    norm_num

/-- Every lower-half spectral cardinality is a divisor of `180` or one of
the twelve explicitly listed exceptional sizes. -/
theorem z180_spectral_cardinality_sieve
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hle : A.card ≤ 90) :
    A.card ∣ 180 ∨
      A.card = 7 ∨ A.card = 8 ∨ A.card = 11 ∨ A.card = 13 ∨
      A.card = 14 ∨ A.card = 16 ∨ A.card = 17 ∨ A.card = 19 ∨
      A.card = 21 ∨ A.card = 24 ∨ A.card = 27 ∨ A.card = 33 := by
  apply z180_cardinality_arithmetic_sieve A.card
  · exact Finset.card_pos.mpr hSpec.1
  · exact hle
  · exact z180_card_le_forty_five_of_spectral_not_two_dvd hSpec
  · exact z180_card_le_twenty_of_spectral_not_three_dvd hSpec
  · exact z180_card_le_thirty_six_of_spectral_not_five_dvd hSpec

#print axioms z180_spectral_cardinality_sieve

end Fuglede
