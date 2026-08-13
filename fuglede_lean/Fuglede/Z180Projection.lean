import Fuglede.PrimeCyclotomic
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-!
# The projection to `ZMod 36` for spectral pairs in `ZMod 180`

If two distinct residues have the same image modulo `36`, their difference
has additive order five.  Spectral duality would then force a fifth
cyclotomic zero on the spectrum, and hence divisibility of the common
cardinality by five.  Consequently, whenever five does not divide the
cardinality, projection to `ZMod 36` is injective on both members of a
spectral pair.

This is the exact justification for the binary capacity constraints used in
the `|A| = 6, 12, 18` descent branches for `ZMod 180`.
-/

namespace Fuglede

/-- A nonzero element in the kernel of `ZMod 180 -> ZMod 36` has order five. -/
theorem z180_frequencyOrder_five_of_cast36_eq :
    ∀ x y : ZMod 180,
      x ≠ y →
      (ZMod.cast x : ZMod 36) = ZMod.cast y →
      frequencyOrder 180 (x - y) = 5 := by
  intro x y hxy hcast
  have hcastZero : (ZMod.cast (x - y) : ZMod 36) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 36 ∣ 180), hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 36) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 36 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 36).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by
    omega
  have hklt : k < 5 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

/-- If five does not divide the cardinality, projection modulo `36` is
injective on the set member of a spectral pair. -/
theorem z180_projection36_injOn_of_spectral_not_five_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : ¬ 5 ∣ A.card) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hdual : CyclotomicSpectrum 180 L A :=
    cyclotomicSpectrum_dual hSpec
  have hzero : CyclotomicZero 180 L (x - y) :=
    hdual.2.2 x hx y hy hxy
  have horder : frequencyOrder 180 (x - y) = 5 :=
    z180_frequencyOrder_five_of_cast36_eq x y hxy hcast
  have hdivL : 5 ∣ L.card :=
    prime_dvd_card_of_cyclotomicZero (by norm_num) L (x - y) horder hzero
  apply hcard
  rw [hSpec.2.1]
  exact hdivL

/-- The same projection is injective on the spectrum member. -/
theorem z180_projection36_spectrum_injOn_of_spectral_not_five_dvd
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : ¬ 5 ∣ A.card) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (L : Set (ZMod 180)) := by
  apply z180_projection36_injOn_of_spectral_not_five_dvd
    (cyclotomicSpectrum_dual hSpec)
  rw [← hSpec.2.1]
  exact hcard

end Fuglede
