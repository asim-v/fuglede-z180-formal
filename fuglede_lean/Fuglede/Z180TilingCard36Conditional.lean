import Fuglede.Z180TilingPrimeAllocation
import Fuglede.Z180K30FibreFourier
import Fuglede.Z180K30OrderClosureSemantic
import Mathlib.Tactic

/-!
# The explicit 36-point spectrum in `ZMod 180`

The frequencies with vanishing fifth CRT coordinate form the dual copy of
`ZMod 36`, obtained by multiplication by five.  Their nonzero differences
have exact orders

`2, 3, 4, 6, 9, 12, 18, 36`.

Consequently, cyclotomic zeros at precisely those eight orders construct a
36-point spectrum.  For a `36 × 5` tiling, prime-power allocation already
supplies orders `2, 3, 4, 9`; the remaining mathematical issue is exactly the
four mixed orders `6, 12, 18, 36`.
-/

namespace Fuglede

/-- The full dual copy of `ZMod 36` inside `ZMod 180`. -/
noncomputable def z180LiftedSpectrum36 : Finset (ZMod 180) :=
  Finset.univ.image z180K30LiftFrequency36

theorem z180K30LiftFrequency36_injective :
    Function.Injective z180K30LiftFrequency36 := by
  intro x y hxy
  have horder : frequencyOrder 36 (x - y) = 1 := by
    rw [← frequencyOrder_z180K30LiftFrequency36]
    have hliftSub :
        z180K30LiftFrequency36 (x - y) =
          z180K30LiftFrequency36 x - z180K30LiftFrequency36 y := by
      revert x y
      decide
    rw [hliftSub, hxy, sub_self]
    rfl
  exact sub_eq_zero.mp
    ((frequencyOrder_eq_one_iff (by norm_num) (x - y)).mp horder)

theorem z180LiftedSpectrum36_card : z180LiftedSpectrum36.card = 36 := by
  classical
  rw [z180LiftedSpectrum36, Finset.card_image_of_injective _
    z180K30LiftFrequency36_injective]
  simp

theorem z180K30LiftFrequency36_sub (x y : ZMod 36) :
    z180K30LiftFrequency36 x - z180K30LiftFrequency36 y =
      z180K30LiftFrequency36 (x - y) := by
  revert x y
  decide

/-- Eight exact-order zeros produce the canonical lifted 36-spectrum. -/
theorem z180_cyclotomicSpectrum_lifted36_of_order_zeros
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 36)
    (h2 : CyclotomicZero 180 A (90 : ZMod 180))
    (h3 : CyclotomicZero 180 A (60 : ZMod 180))
    (h4 : CyclotomicZero 180 A (45 : ZMod 180))
    (h6 : CyclotomicZero 180 A (30 : ZMod 180))
    (h9 : CyclotomicZero 180 A (20 : ZMod 180))
    (h12 : CyclotomicZero 180 A (15 : ZMod 180))
    (h18 : CyclotomicZero 180 A (10 : ZMod 180))
    (h36 : CyclotomicZero 180 A (5 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180LiftedSpectrum36 := by
  classical
  refine ⟨hA, hcard.trans z180LiftedSpectrum36_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180LiftedSpectrum36, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hlne rfl
  rw [z180K30LiftFrequency36_sub]
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have horderNeOne : frequencyOrder 36 (x - y) ≠ 1 := by
    intro hone
    exact hne ((frequencyOrder_eq_one_iff (by norm_num) (x - y)).mp hone)
  have hdiv : frequencyOrder 36 (x - y) ∣ 36 :=
    frequencyOrder_dvd_modulus (x - y)
  have hr2 : frequencyOrder 180 (90 : ZMod 180) = 2 := by decide
  have hr3 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have hr4 : frequencyOrder 180 (45 : ZMod 180) = 4 := by decide
  have hr6 : frequencyOrder 180 (30 : ZMod 180) = 6 := by decide
  have hr9 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have hr12 : frequencyOrder 180 (15 : ZMod 180) = 12 := by decide
  have hr18 : frequencyOrder 180 (10 : ZMod 180) = 18 := by decide
  have hr36 : frequencyOrder 180 (5 : ZMod 180) = 36 := by decide
  have hcases := eq_one_or_eight_nontrivial_divisors_of_36 hdiv
  rcases hcases with h1 | h2' | h3' | h4' | h6' | h9' | h12' | h18' | h36'
  · exact (horderNeOne h1).elim
  · unfold CyclotomicZero at h2 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h2']
    rw [hr2] at h2
    exact h2
  · unfold CyclotomicZero at h3 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h3']
    rw [hr3] at h3
    exact h3
  · unfold CyclotomicZero at h4 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h4']
    rw [hr4] at h4
    exact h4
  · unfold CyclotomicZero at h6 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h6']
    rw [hr6] at h6
    exact h6
  · unfold CyclotomicZero at h9 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h9']
    rw [hr9] at h9
    exact h9
  · unfold CyclotomicZero at h12 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h12']
    rw [hr12] at h12
    exact h12
  · unfold CyclotomicZero at h18 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h18']
    rw [hr18] at h18
    exact h18
  · unfold CyclotomicZero at h36 ⊢
    rw [frequencyOrder_z180K30LiftFrequency36, h36']
    rw [hr36] at h36
    exact h36

/-- The `36 × 5` tiling case, reduced exactly to its four mixed-order zeros. -/
theorem z180_exists_spectrum_of_tile_card_thirty_six_of_mixed_order_zeros
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36)
    (h6 : CyclotomicZero 180 A (30 : ZMod 180))
    (h12 : CyclotomicZero 180 A (15 : ZMod 180))
    (h18 : CyclotomicZero 180 A (10 : ZMod 180))
    (h36 : CyclotomicZero 180 A (5 : ZMod 180)) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨h2, h3, h4, h9, -⟩ :=
    z180_tile_card_thirty_six_primePower_zeros hTiles hcard
  refine ⟨z180LiftedSpectrum36,
    z180_cyclotomicSpectrum_lifted36_of_order_zeros ?_ hcard
      h2 h3 h4 h6 h9 h12 h18 h36⟩
  apply Finset.card_pos.mp
  omega

#print axioms z180_cyclotomicSpectrum_lifted36_of_order_zeros
#print axioms z180_exists_spectrum_of_tile_card_thirty_six_of_mixed_order_zeros

end Fuglede
