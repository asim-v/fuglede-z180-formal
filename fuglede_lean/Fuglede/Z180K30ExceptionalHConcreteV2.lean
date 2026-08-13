import Fuglede.Z180K30SixLevelFourierV4

/-!
# Concrete H-cosets in the exceptional K30 branch
-/

namespace Fuglede

def z36K30Projection6 : ZMod 36 →+ ZMod 6 :=
  (ZMod.castHom (by norm_num : 6 ∣ 36) (ZMod 6)).toAddMonoidHom

@[simp]
theorem z36K30Projection6_apply (x : ZMod 36) :
    z36K30Projection6 x = ZMod.cast x := rfl

def Z180K30HCosetColumnConcrete
    (L : Finset (ZMod 180)) (s : Fin 5) : Prop :=
  ∃ ρ : ZMod 6,
    z180K30FifthFibres36 L s =
      (Finset.univ : Finset (ZMod 36)).filter
        (fun q ↦ z36K30Projection6 q = ρ)

def Z180K30AllHCosetColumnsConcrete (L : Finset (ZMod 180)) : Prop :=
  ∀ s : Fin 5, Z180K30HCosetColumnConcrete L s

def Z180K30Projection30Saturated (L : Finset (ZMod 180)) : Prop :=
  ∀ l ∈ L, ∀ b : ZMod 6, l + z180K30Kernel30Lift b ∈ L

def z180K30FinOfZMod5 (c : ZMod 5) : Fin 5 :=
  ⟨c.val, c.val_lt⟩

@[simp]
theorem z180K30FinOfZMod5_cast (c : ZMod 5) :
    ((z180K30FinOfZMod5 c).val : ZMod 5) = c := by
  exact ZMod.natCast_zmod_val c

theorem z180K30_kernel30Lift_preserves_H_coordinates :
    ∀ l : ZMod 180, ∀ b : ZMod 6,
      (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 5) = ZMod.cast l ∧
      z36K30Projection6
          (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 36) =
        z36K30Projection6 (ZMod.cast l : ZMod 36) := by
  decide

theorem z180K30_projection30_eq_iff_exists_kernel30Lift :
    ∀ x y : ZMod 180,
      z180K30Projection30 x = z180K30Projection30 y ↔
        ∃ b : ZMod 6, x = y + z180K30Kernel30Lift b := by
  decide

theorem z180K30_kernel30_translate_injective :
    ∀ y : ZMod 180,
      Function.Injective (fun b : ZMod 6 ↦ y + z180K30Kernel30Lift b) := by
  decide

theorem z180_k30_projection30_saturated_of_all_HCosetColumns
    {L : Finset (ZMod 180)}
    (hH : Z180K30AllHCosetColumnsConcrete L) :
    Z180K30Projection30Saturated L := by
  classical
  intro l hl b
  let c5 : ZMod 5 := ZMod.cast l
  let s : Fin 5 := z180K30FinOfZMod5 c5
  rcases hH s with ⟨ρ, hcolumn⟩
  have hs : (s.val : ZMod 5) = c5 := by
    simp [s]
  have hl36 : (ZMod.cast l : ZMod 36) ∈ z180K30FifthFibres36 L s := by
    exact Finset.mem_image.mpr ⟨l,
      Finset.mem_filter.mpr ⟨hl, hs.symm⟩, rfl⟩
  have hlρ : z36K30Projection6 (ZMod.cast l : ZMod 36) = ρ := by
    rw [hcolumn] at hl36
    exact (Finset.mem_filter.mp hl36).2
  let y : ZMod 180 := l + z180K30Kernel30Lift b
  have hycoords := z180K30_kernel30Lift_preserves_H_coordinates l b
  have hy36 : (ZMod.cast y : ZMod 36) ∈ z180K30FifthFibres36 L s := by
    rw [hcolumn]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [y] using hycoords.2.trans hlρ
  obtain ⟨x, hxfilter, hxy36⟩ := Finset.mem_image.mp hy36
  have hx := (Finset.mem_filter.mp hxfilter).1
  have hx5 := (Finset.mem_filter.mp hxfilter).2
  have hxy : x = y := by
    apply z180K30CRT.injective
    rw [z180K30CRT_apply, z180K30CRT_apply]
    apply Prod.ext
    · exact hx5.trans (hs.trans hycoords.1.symm)
    · exact hxy36
  rwa [← hxy]

theorem z180_k30_projection30_fibre_card_six_of_saturated
    {L : Finset (ZMod 180)}
    (hsat : Z180K30Projection30Saturated L)
    {l : ZMod 180} (hl : l ∈ L) :
    (L.filter fun x ↦ z180K30Projection30 x =
      z180K30Projection30 l).card = 6 := by
  classical
  have heq :
      L.filter (fun x ↦ z180K30Projection30 x =
        z180K30Projection30 l) =
      (Finset.univ : Finset (ZMod 6)).image
        (fun b ↦ l + z180K30Kernel30Lift b) := by
    ext x
    constructor
    · intro hx
      have hxproj := (Finset.mem_filter.mp hx).2
      rcases (z180K30_projection30_eq_iff_exists_kernel30Lift x l).mp hxproj with
        ⟨b, rfl⟩
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
    · intro hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hsat l hl b, ?_⟩
      simp [map_add, z180K30Projection30_kernel30Lift]
  rw [heq, Finset.card_image_of_injective _
    (z180K30_kernel30_translate_injective l)]
  decide

theorem z180_k30_projection30_image_card_five_of_saturated
    {L : Finset (ZMod 180)}
    (hsat : Z180K30Projection30Saturated L) (hcard : L.card = 30) :
    (L.image z180K30Projection30).card = 5 := by
  classical
  let R := L.image z180K30Projection30
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := L) (t := R) (f := z180K30Projection30) (by
      intro l hl
      exact Finset.mem_image_of_mem z180K30Projection30 hl)
  have hfibre : ∀ r ∈ R,
      (L.filter fun x ↦ z180K30Projection30 x = r).card = 6 := by
    intro r hr
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
    exact z180_k30_projection30_fibre_card_six_of_saturated hsat hl
  have hmass : 30 = 6 * R.card := by
    calc
      30 = L.card := hcard.symm
      _ = ∑ r ∈ R,
          (L.filter fun x ↦ z180K30Projection30 x = r).card := hpartition
      _ = ∑ r ∈ R, 6 := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hfibre r hr
      _ = 6 * R.card := by simp
  change R.card = 5
  omega

def z180K30ExactExceptionalCertificateOfConcreteH
    {A L : Finset (ZMod 180)}
    {boundary : Z180K30ExceptionalExternalBoundary A L}
    (hcert : ∀ s, boundary.ResidueCandidate s →
      Z180K30HCosetColumnConcrete L s) :
    Z180K30ExactExceptionalCertificate boundary where
  HCosetColumn := Z180K30HCosetColumnConcrete L
  certifiedOnlyH := hcert

#print axioms z180_k30_projection30_saturated_of_all_HCosetColumns
#print axioms z180_k30_projection30_image_card_five_of_saturated

end Fuglede
