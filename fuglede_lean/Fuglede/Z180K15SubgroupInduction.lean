import Fuglede.Z180K15ModTwoDescent
import Mathlib.Tactic

/-!
# The exact subgroup-induction interface for the `|S| = 15` case

This module continues the specialization of FKMS Section 3.3 after the
finite-field obstruction.  It makes two points precise.

* Failure of the projected `Phi_3` factor already forces injectivity modulo
  fifteen, hence gives an unconditional tiling of `ZMod 180`.
* Projection modulo forty-five preserves the cardinality of both sides of
  the spectral pair, but preservation of the cyclotomic zeros is a separate
  hypothesis.  We package exactly that hypothesis and prove that it is
  sufficient for the cardinality-fifteen induction step in `ZMod 45`.

The final reduction theorem leaves only the projected `Phi_9`, `Phi_15`, and
`Phi_45` branches.  No tiling conclusion for those branches is asserted.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Direct characteristic-two reduction of an integer cyclotomic divisor.
This is the odd-index companion to the twice-index bridge. -/
theorem cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask
    {m : Nat} (hm45 : m ∣ 45) {S : Finset (ZMod 180)}
    (hdiv : cyclotomic m Int ∣ maskPolynomial 180 S) :
    cyclotomic m (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mapped_mask hm45
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 2)) hdiv
  rw [map_cyclotomic] at hmap
  exact hmap

/-- The `2^2 m` case of characteristic-two cyclotomic reduction. -/
theorem cyclotomic_mod_two_dvd_of_four_times_index_dvd
    {m : Nat} (hm : ¬ 2 ∣ m) {P : Polynomial Int}
    (hdiv : cyclotomic (4 * m) Int ∣ P) :
    cyclotomic m (ZMod 2) ∣ P.map (Int.castRingHom (ZMod 2)) := by
  have hmap := Polynomial.map_dvd (Int.castRingHom (ZMod 2)) hdiv
  rw [map_cyclotomic] at hmap
  have hpow :
      cyclotomic (4 * m) (ZMod 2) =
        cyclotomic m (ZMod 2) ^ 2 := by
    simpa using
      (cyclotomic_mul_prime_pow_eq (ZMod 2) hm
        (k := 2) (by norm_num))
  rw [hpow] at hmap
  exact (dvd_pow_self (cyclotomic m (ZMod 2)) (by norm_num)).trans hmap

/-- Projection form of the preceding `2^2 m` reduction. -/
theorem cyclotomic_dvd_projection45MaskModTwo_of_four_times_index_dvd_mask
    {m : Nat} (hm : ¬ 2 ∣ m) (hm45 : m ∣ 45)
    {S : Finset (ZMod 180)}
    (hdiv : cyclotomic (4 * m) Int ∣ maskPolynomial 180 S) :
    cyclotomic m (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mapped_mask hm45
  exact cyclotomic_mod_two_dvd_of_four_times_index_dvd hm hdiv

/-- The sealed order-five gateway supplies the `Phi_5` factor of each
projected mask. -/
theorem z180_k15_projection45_phi5_dvd_both
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    cyclotomic 5 (ZMod 2) ∣ z180Projection45MaskModTwo A ∧
      cyclotomic 5 (ZMod 2) ∣ z180Projection45MaskModTwo L := by
  obtain ⟨hA, hL⟩ := z180_phi5_k15_both_cyclotomic_zero hSpec hcard
  have horder36 : frequencyOrder 180 (36 : ZMod 180) = 5 := by decide
  constructor
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, horder36] using hA
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, horder36] using hL

/-- If two residues agree modulo fifteen but not modulo forty-five, their
difference in `ZMod 180` has order `3`, `6`, or `12`. -/
theorem z180_frequencyOrder_three_six_or_twelve_of_cast15_eq_of_cast45_ne
    (x y : ZMod 180)
    (hcast15 : (ZMod.cast x : ZMod 15) = ZMod.cast y)
    (hcast45 : z180K15Projection45 x ≠ z180K15Projection45 y) :
    frequencyOrder 180 (x - y) = 3 ∨
      frequencyOrder 180 (x - y) = 6 ∨
      frequencyOrder 180 (x - y) = 12 := by
  have hcast15Zero : (ZMod.cast (x - y) : ZMod 15) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 15 ∣ 180), hcast15, sub_self]
  have hnatCast15Zero : ((x - y).val : ZMod 15) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcast15Zero
  have hdvd : 15 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 15).1 hnatCast15Zero
  obtain ⟨k, hk⟩ := hdvd
  have hcast45Diff : (ZMod.cast (x - y) : ZMod 45) ≠ 0 := by
    intro hzero
    apply hcast45
    change (ZMod.cast x : ZMod 45) = ZMod.cast y
    rw [← sub_eq_zero]
    simpa [ZMod.cast_sub (by norm_num : 45 ∣ 180)] using hzero
  have hnatCast45Diff : ((x - y).val : ZMod 45) ≠ 0 := by
    simpa only [ZMod.cast_eq_val] using hcast45Diff
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    apply hnatCast45Diff
    rw [hzero]
    norm_num
  have hkpos : 0 < k := by omega
  have hklt : k < 12 := by
    have hvalLt := (x - y).val_lt
    omega
  have hnotdvd45 : ¬ 45 ∣ 15 * k := by
    intro hdiv45
    apply hnatCast45Diff
    rw [hk]
    exact (ZMod.natCast_eq_zero_iff (15 * k) 45).2 hdiv45
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos hnotdvd45
  all_goals norm_num

/-- Orders `3`, `6`, and `12` all reduce to the projected `Phi_3` factor in
characteristic two. -/
theorem cyclotomic_three_dvd_projection45MaskModTwo_of_order_three_six_or_twelve
    {S : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 3 ∨
      frequencyOrder 180 d = 6 ∨ frequencyOrder 180 d = 12)
    (hzero : CyclotomicZero 180 S d) :
    cyclotomic 3 (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  rcases horder with hthree | hsix | htwelve
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, hthree] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 3) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, hsix] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_four_times_index_dvd_mask
      (m := 3) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, htwelve] using hzero

/-- In the missing-`Phi_3` branch, reduction modulo fifteen is injective on
the spectral set. -/
theorem z180_k15_projection15_injOn_of_not_phi3_dvd_projection45_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot3 : ¬ cyclotomic 3 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 15))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast15
  by_contra hxy
  have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
  have hcast45 : z180K15Projection45 x ≠ z180K15Projection45 y := by
    intro hcast
    exact hxy (hinj45 hx hy hcast)
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  apply hnot3
  exact cyclotomic_three_dvd_projection45MaskModTwo_of_order_three_six_or_twelve
    (z180_frequencyOrder_three_six_or_twelve_of_cast15_eq_of_cast45_ne
      x y hcast15 hcast45) hzero

/-- The missing-`Phi_3` branch of the FKMS split closes unconditionally:
`A` is a transversal modulo fifteen and therefore tiles by the projection
kernel. -/
theorem z180_k15_exists_tiling_of_not_phi3_dvd_projection45_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot3 : ¬ cyclotomic 3 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k15_exists_tiling_of_projection15_injOn hcard
  exact
    z180_k15_projection15_injOn_of_not_phi3_dvd_projection45_spectrum_mask
      hSpec hcard hnot3

/-- Exact zero-descent condition needed to turn the two injective images in
`ZMod 45` into a cyclotomic spectral pair.  It is not implied merely by
injectivity: the discarded `ZMod 4` phase must also be controlled. -/
def Z180K15Projection45ZeroDescends
    (A L : Finset (ZMod 180)) : Prop :=
  ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
    CyclotomicZero 45 (A.image z180K15Projection45)
      (z180K15Projection45 l₁ - z180K15Projection45 l₂)

/-- Under the exact zero-descent condition, the projected images form a
genuine cyclotomic spectrum in `ZMod 45`. -/
theorem z180_k15_projection45_cyclotomicSpectrum_of_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hdesc : Z180K15Projection45ZeroDescends A L) :
    CyclotomicSpectrum 45
      (A.image z180K15Projection45) (L.image z180K15Projection45) := by
  obtain ⟨hinjA, hinjL, -, -⟩ := z180_k15_fkms_qr_gateway hSpec hcard
  refine ⟨hSpec.1.image z180K15Projection45, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinjA,
      Finset.card_image_of_injOn hinjL]
    exact hSpec.2.1
  · intro l₁ hl₁ l₂ hl₂ hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl₁
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl₂
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hne rfl
    exact hdesc x hx y hy hxy

/-- The zero-descent condition is not merely sufficient: after the gateway
it is exactly the remaining orthogonality field of the projected spectrum. -/
theorem z180_k15_projection45_cyclotomicSpectrum_iff_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    CyclotomicSpectrum 45
        (A.image z180K15Projection45) (L.image z180K15Projection45) ↔
      Z180K15Projection45ZeroDescends A L := by
  constructor
  · intro himage l₁ hl₁ l₂ hl₂ hne
    have hinjL := (z180_k15_fkms_qr_gateway hSpec hcard).2.1
    have hneImage : z180K15Projection45 l₁ ≠ z180K15Projection45 l₂ := by
      intro heq
      exact hne (hinjL hl₁ hl₂ heq)
    exact himage.2.2 _ (Finset.mem_image_of_mem _ hl₁)
      _ (Finset.mem_image_of_mem _ hl₂) hneImage
  · exact z180_k15_projection45_cyclotomicSpectrum_of_zero_descent
      hSpec hcard

/-- The cardinality-specific induction hypothesis actually needed at
modulus forty-five. -/
def Z45SpectralCard15ImpliesTile : Prop :=
  ∀ A L : Finset (ZMod 45), A.card = 15 →
    CyclotomicSpectrum 45 A L → ∃ B : Finset (ZMod 45), Tiles A B

/-- Exact conditional subgroup-induction endpoint: zero descent plus the
cardinality-fifteen theorem in `ZMod 45` tiles the original set. -/
theorem z180_k15_exists_tiling_of_projection45_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hdesc : Z180K15Projection45ZeroDescends A L)
    (hInduction : Z45SpectralCard15ImpliesTile) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hinjA := (z180_k15_fkms_qr_gateway hSpec hcard).1
  have himageCard : (A.image z180K15Projection45).card = 15 := by
    rw [Finset.card_image_of_injOn hinjA, hcard]
  have himageSpec :=
    z180_k15_projection45_cyclotomicSpectrum_of_zero_descent
      hSpec hcard hdesc
  obtain ⟨C, hC⟩ := hInduction _ _ himageCard himageSpec
  exact z180_k15_exists_tiling_of_projection45_image_tile
    hSpec hcard ⟨C, hC⟩

/-- The finite-field obstruction and the sealed `Phi_5` gateway reduce the
unresolved local argument to exactly three factors, unless the already
closed `Phi_3` branch tiles. -/
theorem z180_k15_tiling_or_remaining_projection45_factor_failure
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      ¬ cyclotomic 9 (ZMod 2) ∣ z180Projection45MaskModTwo L ∨
      ¬ cyclotomic 15 (ZMod 2) ∣ z180Projection45MaskModTwo L ∨
      ¬ cyclotomic 45 (ZMod 2) ∣ z180Projection45MaskModTwo L := by
  have hcardL : L.card = 15 := hSpec.2.1.symm.trans hcard
  have h5 := (z180_k15_projection45_phi5_dvd_both hSpec hcard).2
  by_cases h3 : cyclotomic 3 (ZMod 2) ∣ z180Projection45MaskModTwo L
  · by_cases h9 : cyclotomic 9 (ZMod 2) ∣ z180Projection45MaskModTwo L
    · by_cases h15 : cyclotomic 15 (ZMod 2) ∣ z180Projection45MaskModTwo L
      · by_cases h45 : cyclotomic 45 (ZMod 2) ∣ z180Projection45MaskModTwo L
        · obtain ⟨k, l, hkl⟩ :=
            z180_card_eq_45_mul_add_two_mul_of_projection45_cyclotomic_divisors
              L h3 h5 h9 h15 h45
          omega
        · exact Or.inr (Or.inr (Or.inr h45))
      · exact Or.inr (Or.inr (Or.inl h15))
    · exact Or.inr (Or.inl h9)
  · exact Or.inl
      (z180_k15_exists_tiling_of_not_phi3_dvd_projection45_spectrum_mask
        hSpec hcard h3)

#print axioms cyclotomic_mod_two_dvd_of_four_times_index_dvd
#print axioms z180_k15_projection15_injOn_of_not_phi3_dvd_projection45_spectrum_mask
#print axioms z180_k15_exists_tiling_of_not_phi3_dvd_projection45_spectrum_mask
#print axioms z180_k15_projection45_cyclotomicSpectrum_of_zero_descent
#print axioms z180_k15_projection45_cyclotomicSpectrum_iff_zero_descent
#print axioms z180_k15_exists_tiling_of_projection45_zero_descent
#print axioms z180_k15_tiling_or_remaining_projection45_factor_failure

end Fuglede
