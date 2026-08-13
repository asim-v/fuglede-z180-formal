import Fuglede.Z180K30ExceptionalHConcreteV3
import Fuglede.Z30K5InflationBridge

namespace Fuglede

open scoped BigOperators ZMod

noncomputable def z180K30ExceptionalResidues30
    (L : Finset (ZMod 180)) : Finset (ZMod 30) :=
  L.image z180K30Projection30

@[simp]
theorem z180K30Projection6_kernel30Lift (b : ZMod 6) :
    z180K30Projection6 (z180K30Kernel30Lift b) = 0 := by
  revert b
  decide

theorem z180K30_projection6_eq_of_projection30_eq
    (x y : ZMod 180)
    (hxy : z180K30Projection30 x = z180K30Projection30 y) :
    z180K30Projection6 x = z180K30Projection6 y := by
  obtain ⟨b, rfl⟩ :=
    (z180K30_projection30_eq_iff_exists_kernel30Lift x y).mp hxy
  simp only [map_add, z180K30Projection6_kernel30Lift, add_zero]

@[simp]
theorem z180K30SixLevelFourierSum_zero
    (X : Finset (ZMod 180)) (c : ZMod 6) :
    z180K30SixLevelFourierSum X 0 c =
      ((z180K30SixthSlice X c).card : ℂ) := by
  simp [z180K30SixLevelFourierSum]

theorem z180_k30_sixthFibre_card_five_of_saturated_spectrum
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hsat : Z180K30Projection30Saturated L) :
    ∀ c : ZMod 6, (z180K30SixthFibre A c).card = 5 := by
  classical
  have hcardL : L.card = 30 := hSpec.2.1.symm.trans hcard
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨l, hl⟩ := hLnonempty
  have hzero : ∀ b : ZMod 6, b ≠ 0 →
      fourierSum A (0 + z180K30Kernel30Lift (-b)) = 0 := by
    intro b hb
    have hlb : l + z180K30Kernel30Lift (-b) ∈ L := hsat l hl (-b)
    have hne : l + z180K30Kernel30Lift (-b) ≠ l := by
      intro heq
      have hzeroLift : z180K30Kernel30Lift (-b) = 0 := by
        exact add_left_cancel (heq.trans (add_zero l).symm)
      have hbzero : -b = 0 := z180K30Kernel30Lift_injective
        (hzeroLift.trans z180K30Kernel30Lift_zero.symm)
      exact hb (neg_eq_zero.mp hbzero)
    have hcyclo := hSpec.2.2
      (l + z180K30Kernel30Lift (-b)) hlb l hl hne
    have hfourier :=
      (cyclotomicZero_iff_fourierSum_zero A _).1 hcyclo
    convert hfourier using 1 <;> ring_nf
  have heqLevel : ∀ c c' : ZMod 6,
      z180K30SixLevelFourierSum A 0 c =
        z180K30SixLevelFourierSum A 0 c' := by
    apply eq_of_dft_eq_zero_off_zero
    intro b hb
    rw [← fourierSum_add_kernel30Lift_eq_dft]
    exact hzero b hb
  have hsum :
      (∑ c : ZMod 6, z180K30SixLevelFourierSum A 0 c) = (30 : ℂ) := by
    rw [sum_z180K30SixLevelFourierSum_eq, fourierSum_zero, hcard]
    norm_num
  intro c
  have hlevel : z180K30SixLevelFourierSum A 0 c = 5 := by
    have hsix : (6 : ℂ) * z180K30SixLevelFourierSum A 0 c = 30 := by
      rw [← hsum]
      simp_rw [heqLevel _ c]
      norm_num
    linear_combination hsix / 6
  have hslice : (z180K30SixthSlice A c).card = 5 := by
    have h := hlevel
    rw [z180K30SixLevelFourierSum_zero] at h
    exact_mod_cast h
  have hinj : Set.InjOn z180K30SixthDigit
      (A.filter (fun x ↦ z180K30Projection6 x = c) : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply z180K30SixthDigit_injective_on_sixth_slice c
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy
  rw [z180K30SixthFibre, Finset.card_image_iff.mpr hinj]
  simpa only [z180K30SixthSlice] using hslice

#print axioms z180_k30_sixthFibre_card_five_of_saturated_spectrum

end Fuglede
