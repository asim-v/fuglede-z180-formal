import Fuglede.Z180K30SixLevelFourier
import Mathlib.Tactic

/-!
# Concrete H-coset condition for the exceptional K30 branch

The subgroup `H = 6 * ZMod 36` is the kernel of reduction
`ZMod 36 -> ZMod 6`.  Thus a projected fifth column is an affine H-coset
exactly when it is one complete residue class modulo six.  This module uses
that concrete statement and proves that `L` is saturated by the six-element
fibres of `z180K30Projection30`.
-/

namespace Fuglede

/-- Reduction `ZMod 36 -> ZMod 6`; its kernel is `6 * ZMod 36`. -/
def z36K30Projection6 : ZMod 36 →+ ZMod 6 :=
  (ZMod.castHom (by norm_num : 6 ∣ 36) (ZMod 6)).toAddMonoidHom

@[simp]
theorem z36K30Projection6_apply (x : ZMod 36) :
    z36K30Projection6 x = ZMod.cast x := rfl

/-- Honest spelling of “the `s`-th projected fifth fibre is an affine coset
of `H = 6 * ZMod 36`”. -/
def Z180K30HCosetColumnConcrete
    (L : Finset (ZMod 180)) (s : Fin 5) : Prop :=
  ∃ ρ : ZMod 6,
    z180K30FifthFibres36 L s =
      (Finset.univ : Finset (ZMod 36)).filter
        (fun q ↦ z36K30Projection6 q = ρ)

/-- All five projected fifth columns are H-cosets. -/
def Z180K30AllHCosetColumnsConcrete (L : Finset (ZMod 180)) : Prop :=
  ∀ s : Fin 5, Z180K30HCosetColumnConcrete L s

/-- Closure under the kernel of reduction modulo thirty. -/
def Z180K30Projection30Saturated (L : Finset (ZMod 180)) : Prop :=
  ∀ l ∈ L, ∀ b : ZMod 6, l + z180K30Kernel30Lift b ∈ L

/-- Canonical conversion of a residue modulo five to the corresponding
`Fin 5` index. -/
def z180K30FinOfZMod5 (c : ZMod 5) : Fin 5 :=
  ⟨c.val, c.val_lt⟩

@[simp]
theorem z180K30FinOfZMod5_cast (c : ZMod 5) :
    ((z180K30FinOfZMod5 c).val : ZMod 5) = c := by
  exact ZMod.natCast_zmod_val c

/-- Adding a kernel-thirty element preserves the fifth coordinate and the
mod-six class of the projected `ZMod 36` coordinate. -/
theorem z180K30_kernel30Lift_preserves_H_coordinates :
    ∀ l : ZMod 180, ∀ b : ZMod 6,
      (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 5) = ZMod.cast l ∧
      z36K30Projection6
          (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 36) =
        z36K30Projection6 (ZMod.cast l : ZMod 36) := by
  decide

/-- Every fibre of reduction modulo thirty is one translate of the six
kernel elements. -/
theorem z180K30_projection30_eq_iff_exists_kernel30Lift :
    ∀ x y : ZMod 180,
      z180K30Projection30 x = z180K30Projection30 y ↔
        ∃ b : ZMod 6, x = y + z180K30Kernel30Lift b := by
  decide

theorem z180K30_kernel30_translate_injective :
    ∀ y : ZMod 180,
      Function.Injective (fun b : ZMod 6 ↦ y + z180K30Kernel30Lift b) := by
  decide

/-- A concrete H-coset in every fifth column makes `L` a union of complete
fibres of reduction modulo thirty. -/
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

/-- Under saturation, every nonempty projection-thirty fibre inside `L` has
exactly six points. -/
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
      have hxL := (Finset.mem_filter.mp hx).1
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

/-- A saturated thirty-point set has exactly five images modulo thirty. -/
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

/-- Tiny adapter that gives the abstract exceptional certificate its honest
H-coset meaning. -/
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
