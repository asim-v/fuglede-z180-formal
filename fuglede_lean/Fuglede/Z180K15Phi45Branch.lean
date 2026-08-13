import Fuglede.Z180K15Phi9Branch
import Mathlib.Tactic

/-!
# The missing-`Phi_45` branch at cardinality fifteen

Absence of the projected `Phi_45` factor prevents two points of the spectral
set from differing in both their modulo-three and modulo-five coordinates.
Since every modulo-five fibre is nonempty, the elementary rook-graph
argument forces the whole set into one modulo-three fibre.  Its injective
image in `ZMod 45` has all fifteen points of that fibre, so it is a translate
of the order-fifteen kernel and tiles.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- If a difference is nonzero in both the modulo-three and modulo-five
coordinates, its order in `ZMod 180` is `45`, `90`, or `180`. -/
theorem z180_frequencyOrder_fortyfive_ninety_or_oneeighty_of_cast3_ne_of_cast5_ne
    (x y : ZMod 180)
    (hcast3 : (ZMod.cast x : ZMod 3) ≠ ZMod.cast y)
    (hcast5 : z180K10FifthCoordinate x ≠ z180K10FifthCoordinate y) :
    frequencyOrder 180 (x - y) = 45 ∨
      frequencyOrder 180 (x - y) = 90 ∨
      frequencyOrder 180 (x - y) = 180 := by
  have hcast3Diff : (ZMod.cast (x - y) : ZMod 3) ≠ 0 := by
    intro hzero
    apply hcast3
    rw [← sub_eq_zero]
    simpa [ZMod.cast_sub (by norm_num : 3 ∣ 180)] using hzero
  have hnotdvd3 : ¬ 3 ∣ (x - y).val := by
    intro hdiv
    apply hcast3Diff
    change ((x - y).val : ZMod 3) = 0
    exact (ZMod.natCast_eq_zero_iff (x - y).val 3).2 hdiv
  have hnotdvd5 : ¬ 5 ∣ (x - y).val := by
    intro hdiv
    apply hcast5
    apply sub_eq_zero.mp
    rw [← z180K10FifthCoordinate_sub]
    rw [z180K10FifthCoordinate, toCRT180_apply]
    change ((x - y).val : ZMod 5) = 0
    exact (ZMod.natCast_eq_zero_iff (x - y).val 5).2 hdiv
  let n := (x - y).val
  change ¬ 3 ∣ n at hnotdvd3
  change ¬ 5 ∣ n at hnotdvd5
  have hc3 : Nat.Coprime 3 n :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hnotdvd3
  have hc5 : Nat.Coprime 5 n :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotdvd5
  have hc45 : Nat.Coprime 45 n := by
    simpa using (hc3.pow_left 2).mul_left hc5
  let g := Nat.gcd 180 n
  have hgdvdn : g ∣ n := Nat.gcd_dvd_right 180 n
  have hgcoprime45 : Nat.Coprime g 45 :=
    hc45.symm.of_dvd_left hgdvdn
  have hgdvd180 : g ∣ 180 := Nat.gcd_dvd_left 180 n
  have hgdvd4 : g ∣ 4 := by
    apply (hgcoprime45.dvd_mul_right).mp
    simpa using hgdvd180
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n (by norm_num)
  have hgcases : g = 1 ∨ g = 2 ∨ g = 4 := by
    have hgle : g ≤ 4 := Nat.le_of_dvd (by norm_num) hgdvd4
    interval_cases g <;> norm_num at *
  change 180 / g = 45 ∨ 180 / g = 90 ∨ 180 / g = 180
  rcases hgcases with hg | hg | hg <;> rw [hg] <;> norm_num

/-- Orders `45`, `90`, and `180` all reduce to the projected `Phi_45`
factor over `F_2`. -/
theorem cyclotomic_fortyfive_dvd_projection45MaskModTwo_of_order_fortyfive_ninety_or_oneeighty
    {S : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 45 ∨
      frequencyOrder 180 d = 90 ∨ frequencyOrder 180 d = 180)
    (hzero : CyclotomicZero 180 S d) :
    cyclotomic 45 (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  rcases horder with h45 | h90 | h180
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, h45] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 45) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, h90] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_four_times_index_dvd_mask
      (m := 45) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, h180] using hzero

/-- Missing `Phi_45` gives the rook-graph relation: every pair in `A`
agrees either modulo three or modulo five. -/
theorem z180_k15_cast3_eq_or_fifthCoordinate_eq_of_not_phi45
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hnot45 : ¬ cyclotomic 45 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ x ∈ A, ∀ y ∈ A,
      (ZMod.cast x : ZMod 3) = ZMod.cast y ∨
        z180K10FifthCoordinate x = z180K10FifthCoordinate y := by
  intro x hx y hy
  by_cases h3 : (ZMod.cast x : ZMod 3) = ZMod.cast y
  · exact Or.inl h3
  by_cases h5 : z180K10FifthCoordinate x = z180K10FifthCoordinate y
  · exact Or.inr h5
  exfalso
  have hxy : x ≠ y := by
    intro h
    subst y
    exact h3 rfl
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  apply hnot45
  apply
    cyclotomic_fortyfive_dvd_projection45MaskModTwo_of_order_fortyfive_ninety_or_oneeighty
      _ hzero
  apply
    z180_frequencyOrder_fortyfive_ninety_or_oneeighty_of_cast3_ne_of_cast5_ne
      x y h3 h5

/-- The balanced fifth fibres turn the preceding pairwise relation into one
global modulo-three fibre. -/
theorem z180_k15_cast3_eq_of_not_phi45
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot45 : ¬ cyclotomic 45 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ x ∈ A, ∀ y ∈ A,
      (ZMod.cast x : ZMod 3) = ZMod.cast y := by
  have hpair :=
    z180_k15_cast3_eq_or_fifthCoordinate_eq_of_not_phi45 hSpec hnot45
  have hocc := (z180_k15_fkms_qr_gateway hSpec hcard).2.2.1
  intro x hx y hy
  by_cases hxy5 : z180K10FifthCoordinate x = z180K10FifthCoordinate y
  · let c : Z180K15FifthCoordinateSpace :=
      z180K10FifthCoordinate x + 1
    have hcne : c ≠ z180K10FifthCoordinate x := by
      have hall : ∀ a : Z180K15FifthCoordinateSpace, a + 1 ≠ a := by
        decide
      simpa [c] using hall (z180K10FifthCoordinate x)
    have hcardFiber :
        (A.filter fun z => z180K10FifthCoordinate z = c).card = 3 := by
      simpa [z180K15FifthOccupancy, z180K10FifthOccupancy] using hocc c
    have hfiberNonempty :
        (A.filter fun z => z180K10FifthCoordinate z = c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty] at hcardFiber
      omega
    obtain ⟨z, hz⟩ := hfiberNonempty
    have hzA : z ∈ A := (Finset.mem_filter.mp hz).1
    have hzcoord : z180K10FifthCoordinate z = c :=
      (Finset.mem_filter.mp hz).2
    have hxz3 : (ZMod.cast x : ZMod 3) = ZMod.cast z := by
      rcases hpair x hx z hzA with h | h
      · exact h
      · exfalso
        apply hcne
        rw [← hzcoord, ← h]
    have hyz3 : (ZMod.cast y : ZMod 3) = ZMod.cast z := by
      rcases hpair y hy z hzA with h | h
      · exact h
      · exfalso
        apply hcne
        rw [← hzcoord, ← h, ← hxy5]
    exact hxz3.trans hyz3.symm
  · rcases hpair x hx y hy with h | h
    · exact h
    · exact False.elim (hxy5 h)

/-- Reduction from `ZMod 45` to its modulo-three quotient. -/
def z45K15Projection3 : ZMod 45 →+ ZMod 3 :=
  (ZMod.castHom (by norm_num : 3 ∣ 45) (ZMod 3)).toAddMonoidHom

@[simp]
theorem card_kernelFinset_z45K15Projection3 :
    (kernelFinset z45K15Projection3).card = 15 := by
  decide

/-- The missing-`Phi_45` branch makes the projected image exactly a
translate of the order-fifteen kernel. -/
theorem z180_k15_projection45_image_eq_translate_kernel3_of_not_phi45
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot45 : ¬ cyclotomic 45 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ a₀ ∈ A.image z180K15Projection45,
      A.image z180K15Projection45 =
        (kernelFinset z45K15Projection3).image (fun h => a₀ + h) := by
  have himageNonempty : (A.image z180K15Projection45).Nonempty :=
    hSpec.1.image z180K15Projection45
  obtain ⟨a₀, ha₀⟩ := himageNonempty
  refine ⟨a₀, ha₀, ?_⟩
  have hall3 := z180_k15_cast3_eq_of_not_phi45 hSpec hcard hnot45
  have hsubset : A.image z180K15Projection45 ⊆
      (kernelFinset z45K15Projection3).image (fun h => a₀ + h) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Finset.mem_image.mp ha₀
    let h : ZMod 45 := z180K15Projection45 x - a₀
    have hh : h ∈ kernelFinset z45K15Projection3 := by
      apply (mem_kernelFinset z45K15Projection3 h).2
      apply AddMonoidHom.mem_ker.mpr
      dsimp [h]
      rw [← hx₀eq]
      rw [map_sub]
      change (ZMod.cast (z180K15Projection45 x) : ZMod 3) -
        ZMod.cast (z180K15Projection45 x₀) = 0
      rw [
        cast_projection45_eq_cast (by norm_num : 3 ∣ 45) x,
        cast_projection45_eq_cast (by norm_num : 3 ∣ 45) x₀,
        hall3 x hx x₀ hx₀, sub_self]
    apply Finset.mem_image.mpr
    refine ⟨h, hh, ?_⟩
    simp [h]
  apply Finset.eq_of_subset_of_card_le hsubset
  have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
  rw [Finset.card_image_of_injective _ (fun _ _ heq => add_left_cancel heq),
    card_kernelFinset_z45K15Projection3,
    Finset.card_image_of_injOn hinj45, hcard]

/-- The projected image tiles `ZMod 45` in the missing-`Phi_45` branch. -/
theorem z180_k15_projection45_image_tiles_of_not_phi45_dvd_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot45 : ¬ cyclotomic 45 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ C : Finset (ZMod 45),
      Tiles (A.image z180K15Projection45) C := by
  obtain ⟨a₀, -, himage⟩ :=
    z180_k15_projection45_image_eq_translate_kernel3_of_not_phi45
      hSpec hcard hnot45
  have hsurj : Function.Surjective z45K15Projection3 := by
    simpa [z45K15Projection3] using
      ZMod.castHom_surjective (by norm_num : 3 ∣ 45)
  obtain ⟨C, hkernel⟩ :=
    exists_kernel_tiling_complement z45K15Projection3 hsurj
  refine ⟨C, ?_⟩
  rw [himage]
  exact tiles_translate_left a₀ hkernel

/-- Lifted tiling conclusion for the missing-`Phi_45` branch. -/
theorem z180_k15_exists_tiling_of_not_phi45_dvd_projection45_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot45 : ¬ cyclotomic 45 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k15_exists_tiling_of_projection45_image_tile hSpec hcard
  exact z180_k15_projection45_image_tiles_of_not_phi45_dvd_spectrum_mask
    hSpec hcard hnot45

#print axioms z180_k15_cast3_eq_of_not_phi45
#print axioms z180_k15_projection45_image_eq_translate_kernel3_of_not_phi45
#print axioms z180_k15_projection45_image_tiles_of_not_phi45_dvd_spectrum_mask
#print axioms z180_k15_exists_tiling_of_not_phi45_dvd_projection45_spectrum_mask

end Fuglede
