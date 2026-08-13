import Fuglede.SpectralFourier
import Fuglede.FiniteTiling
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Cardinality endpoints

Elementary endpoint cases for finite tilings, together with the standard
half-cardinality bound for a proper spectral subset of a finite cyclic group.
-/

namespace Fuglede

/-- A finset in a finite type having full cardinality is the whole type. -/
theorem full_cardinality_eq_univ {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} (hA : A.card = Fintype.card α) :
    A = Finset.univ := by
  exact A.card_eq_iff_eq_univ.mp hA

section TilingEndpoints

variable {G : Type*} [AddGroup G] [Fintype G]

/-- The whole group tiles with the singleton containing zero. -/
theorem tiles_univ_singleton_zero :
    Tiles (Finset.univ : Finset G) {0} := by
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hsum
    have hb : b = 0 := by simpa using (Finset.mem_product.mp hab).2
    have hb' : b' = 0 := by simpa using (Finset.mem_product.mp hab').2
    subst b
    subst b'
    simp only [sumMap, add_zero] at hsum
    apply Subtype.ext
    exact Prod.ext hsum rfl
  · intro g
    refine ⟨⟨(g, 0), by simp⟩, ?_⟩
    simp [sumMap]

/-- The singleton containing zero tiles with the whole group. -/
theorem tiles_singleton_zero_univ :
    Tiles ({0} : Finset G) Finset.univ := by
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hsum
    have ha : a = 0 := by simpa using (Finset.mem_product.mp hab).1
    have ha' : a' = 0 := by simpa using (Finset.mem_product.mp hab').1
    subst a
    subst a'
    simp only [sumMap, zero_add] at hsum
    apply Subtype.ext
    exact Prod.ext rfl hsum
  · intro g
    refine ⟨⟨(0, g), by simp⟩, ?_⟩
    simp [sumMap]

end TilingEndpoints

section ProperSpectralBound

open scoped ComplexConjugate InnerProductSpace

variable {N : ℕ} [NeZero N]

/-- A character column restricted to the complement of `A`. -/
noncomputable def complementCharacter (A : Finset (ZMod N)) (l : ZMod N) :
    EuclideanSpace ℂ ↥Aᶜ :=
  WithLp.toLp 2 (fun x : ↥Aᶜ => ZMod.stdAddChar (x.1 * l))

private theorem sum_subtype_eq_sum_finset {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (∑ x : ↥s, f x.1) = ∑ x ∈ s, f x := by
  simpa only [Finset.univ_eq_attach] using Finset.sum_attach s f

private theorem total_fourier_character_sum_zero (d : ZMod N) (hd : d ≠ 0) :
    (∑ x : ZMod N, ZMod.stdAddChar (x * d)) = 0 := by
  simpa [hd] using
    (AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar N))

private theorem complementCharacter_ne_zero (A : Finset (ZMod N))
    (hA : A ≠ Finset.univ) (l : ZMod N) :
    complementCharacter A l ≠ 0 := by
  have hAc : Aᶜ.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hAc
    exact hA ((Finset.compl_eq_empty_iff A).mp hAc)
  obtain ⟨x, hx⟩ := hAc
  intro hzero
  have heval := congrArg
    (fun v : EuclideanSpace ℂ ↥Aᶜ => v ⟨x, hx⟩) hzero
  simp only [complementCharacter, PiLp.toLp_apply] at heval
  rw [ZMod.stdAddChar_apply] at heval
  exact Circle.coe_ne_zero _ heval

private theorem complementCharacter_inner_eq_zero
    (A L : Finset (ZMod N))
    (horth : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum A (l₁ - l₂) = 0)
    (l₁ l₂ : ↥L) (hne : l₁ ≠ l₂) :
    ⟪complementCharacter A l₁.1, complementCharacter A l₂.1⟫_ℂ = 0 := by
  have hval : l₂.1 ≠ l₁.1 := by
    intro h
    apply hne
    exact Subtype.ext h.symm
  have hdiff : l₂.1 - l₁.1 ≠ 0 := sub_ne_zero.mpr hval
  have hAZero : fourierSum A (l₂.1 - l₁.1) = 0 :=
    horth l₂.1 l₂.2 l₁.1 l₁.2 hval
  have htotal := total_fourier_character_sum_zero (l₂.1 - l₁.1) hdiff
  rw [← A.sum_add_sum_compl
    (fun x : ZMod N => ZMod.stdAddChar (x * (l₂.1 - l₁.1)))] at htotal
  have hcomp :
      (∑ x ∈ Aᶜ, ZMod.stdAddChar (x * (l₂.1 - l₁.1))) = 0 := by
    have hAfin :
        (∑ x ∈ A, ZMod.stdAddChar (x * (l₂.1 - l₁.1))) = 0 := by
      rw [← sum_subtype_eq_sum_finset]
      exact hAZero
    rw [hAfin, zero_add] at htotal
    exact htotal
  rw [PiLp.inner_apply]
  change (∑ x : ↥Aᶜ,
    ⟪ZMod.stdAddChar (x.1 * l₁.1),
      ZMod.stdAddChar (x.1 * l₂.1)⟫_ℂ) = 0
  calc
    (∑ x : ↥Aᶜ,
        ⟪ZMod.stdAddChar (x.1 * l₁.1),
          ZMod.stdAddChar (x.1 * l₂.1)⟫_ℂ) =
        ∑ x ∈ Aᶜ,
          ⟪ZMod.stdAddChar (x * l₁.1),
            ZMod.stdAddChar (x * l₂.1)⟫_ℂ :=
      sum_subtype_eq_sum_finset Aᶜ
        (fun x : ZMod N =>
          ⟪ZMod.stdAddChar (x * l₁.1),
            ZMod.stdAddChar (x * l₂.1)⟫_ℂ)
    _ = ∑ x ∈ Aᶜ, ZMod.stdAddChar (x * (l₂.1 - l₁.1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [RCLike.inner_apply', ← Complex.star_def, star_stdAddChar,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = 0 := hcomp

/-- A proper spectral subset of a finite cyclic group occupies at most half
the group.  The proof restricts its orthogonal character columns to the
complement and applies finite-dimensional linear independence. -/
theorem proper_fourierSpectrum_card_le_half
    {A L : Finset (ZMod N)} (h : FourierSpectrum A L)
    (hproper : A ≠ Finset.univ) :
    2 * A.card ≤ Fintype.card (ZMod N) := by
  rcases h with ⟨hA, hcard, horth⟩
  let v : ↥L → EuclideanSpace ℂ ↥Aᶜ :=
    fun l => complementCharacter A l.1
  have hv_ne : ∀ l, v l ≠ 0 := by
    intro l
    exact complementCharacter_ne_zero A hproper l.1
  have hv_orth : Pairwise fun l₁ l₂ => ⟪v l₁, v l₂⟫_ℂ = 0 := by
    intro l₁ l₂ hne
    exact complementCharacter_inner_eq_zero A L horth l₁ l₂ hne
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hv_ne hv_orth
  have hle : A.card ≤ Aᶜ.card := by
    have hdim := hli.fintype_card_le_finrank
    have hLle : L.card ≤ Aᶜ.card := by
      simpa only [Fintype.card_coe, finrank_euclideanSpace] using hdim
    rw [hcard]
    exact hLle
  calc
    2 * A.card = A.card + A.card := by omega
    _ ≤ A.card + Aᶜ.card := Nat.add_le_add_left hle A.card
    _ = Fintype.card (ZMod N) := Finset.card_add_card_compl A

end ProperSpectralBound

end Fuglede
