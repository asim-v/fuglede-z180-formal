import Fuglede.Z180K15Phi9Branch
import Mathlib.Tactic

/-!
# Reduction of the `|S| = 15` descent to `Phi_15` and `Phi_45`

The finite-field obstruction says that one of the five odd projected factors
is missing.  The order-five factor is present by the sealed gateway, while
the missing-`Phi_3` and missing-`Phi_9` branches now both give explicit
tilings of the image in `ZMod 45`.  Thus only `Phi_15` and `Phi_45` remain.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Fixed reduction from `ZMod 45` to `ZMod 15`. -/
def z45K15Projection15 : ZMod 45 →+ ZMod 15 :=
  (ZMod.castHom (by norm_num : 15 ∣ 45) (ZMod 15)).toAddMonoidHom

/-- In the missing-`Phi_3` branch, the projected image is a complete
transversal modulo fifteen and tiles `ZMod 45` by the three-point kernel. -/
theorem z180_k15_projection45_image_tiles_of_not_phi3_dvd_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot3 : ¬ cyclotomic 3 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    Tiles (A.image z180K15Projection45)
      (kernelFinset z45K15Projection15) := by
  have hinjA :=
    z180_k15_projection15_injOn_of_not_phi3_dvd_projection45_spectrum_mask
      hSpec hcard hnot3
  have hinjImage :
      Set.InjOn z45K15Projection15
        (A.image z180K15Projection45 : Set (ZMod 45)) := by
    intro a ha a' ha' heq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha'
    have hcast15 : (ZMod.cast x : ZMod 15) = ZMod.cast y := by
      rw [← cast_projection45_eq_cast (by norm_num : 15 ∣ 45) x,
        ← cast_projection45_eq_cast (by norm_num : 15 ∣ 45) y]
      exact heq
    rw [hinjA hx hy hcast15]
  apply transversal_tiles_kernel z45K15Projection15
    (A.image z180K15Projection45)
  · exact (kernel_difference_free_iff_injOn z45K15Projection15 _).2
      hinjImage
  · have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
    rw [Finset.card_image_of_injOn hinj45, hcard]
    rfl

/-- Exact two-factor reduction on the projected image.  The left branch is
an explicit tiling in `ZMod 45`; the right branches name the only two local
factor failures not yet closed. -/
theorem z180_k15_projection45_image_tiling_or_phi15_or_phi45_failure
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    (∃ C : Finset (ZMod 45),
      Tiles (A.image z180K15Projection45) C) ∨
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
        · exact Or.inr (Or.inr h45)
      · exact Or.inr (Or.inl h15)
    · exact Or.inl ⟨z45K15Phi9Complement,
        z180_k15_projection45_image_tiles_of_not_phi9_dvd_spectrum_mask
          hSpec hcard h9⟩
  · exact Or.inl ⟨kernelFinset z45K15Projection15,
      z180_k15_projection45_image_tiles_of_not_phi3_dvd_spectrum_mask
        hSpec hcard h3⟩

/-- Lifted form of the exact two-factor reduction in `ZMod 180`. -/
theorem z180_k15_tiling_or_phi15_or_phi45_projection_failure
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      ¬ cyclotomic 15 (ZMod 2) ∣ z180Projection45MaskModTwo L ∨
      ¬ cyclotomic 45 (ZMod 2) ∣ z180Projection45MaskModTwo L := by
  rcases z180_k15_projection45_image_tiling_or_phi15_or_phi45_failure
      hSpec hcard with himage | h15 | h45
  · exact Or.inl
      (z180_k15_exists_tiling_of_projection45_image_tile hSpec hcard himage)
  · exact Or.inr (Or.inl h15)
  · exact Or.inr (Or.inr h45)

#print axioms z180_k15_projection45_image_tiles_of_not_phi3_dvd_spectrum_mask
#print axioms z180_k15_projection45_image_tiling_or_phi15_or_phi45_failure
#print axioms z180_k15_tiling_or_phi15_or_phi45_projection_failure

end Fuglede
