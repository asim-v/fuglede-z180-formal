import Fuglede.SpectralFourier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A Fourier-zero cover certifies a finite cyclic tiling

For subsets `A, B` of `ZMod N`, suppose `|A| |B| = N` and at every nonzero
frequency at least one of the two mask Fourier sums vanishes.  Fourier
inversion then says that every group element has exactly one representation
as `a + b`; hence `A` tiles with complement `B`.

This is the reusable bridge needed when a branch computation produces a
fixed complement by covering all nontrivial character orders.  The proof is
exact and uses the standard additive character; it contains no numerical
root-of-unity evaluation.
-/

namespace Fuglede

open scoped BigOperators

variable {N : ℕ}

/-- Pairs in `A × B` which represent a specified group element. -/
def representationFinset (A B : Finset (ZMod N)) (g : ZMod N) :
    Finset (ZMod N × ZMod N) :=
  (A ×ˢ B).filter fun p ↦ p.1 + p.2 = g

@[simp]
theorem mem_representationFinset {A B : Finset (ZMod N)}
    {g : ZMod N} {p : ZMod N × ZMod N} :
    p ∈ representationFinset A B g ↔
      p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = g := by
  simp [representationFinset, and_assoc]

/-- If every element has exactly one representing pair, the addition map is
bijective, which is precisely `Tiles`. -/
theorem tiles_of_representation_card_eq_one
    (A B : Finset (ZMod N))
    (hrep : ∀ g, (representationFinset A B g).card = 1) :
    Tiles A B := by
  constructor
  · intro p q hpq
    let g : ZMod N := sumMap A B p
    have hp_mem : p.1 ∈ representationFinset A B g := by
      apply mem_representationFinset.mpr
      have hp_prod := Finset.mem_product.mp p.2
      exact ⟨hp_prod.1, hp_prod.2, rfl⟩
    have hq_mem : q.1 ∈ representationFinset A B g := by
      apply mem_representationFinset.mpr
      have hq_prod := Finset.mem_product.mp q.2
      refine ⟨hq_prod.1, hq_prod.2, ?_⟩
      simpa [g, sumMap] using hpq.symm
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (hrep g)
    rw [hr] at hp_mem hq_mem
    simp only [Finset.mem_singleton] at hp_mem hq_mem
    exact Subtype.ext (hp_mem.trans hq_mem.symm)
  · intro g
    have hpos : 0 < (representationFinset A B g).card := by
      rw [hrep g]
      norm_num
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hp' := (mem_representationFinset.mp hp)
    refine ⟨⟨p, Finset.mem_product.mpr ⟨hp'.1, hp'.2.1⟩⟩, ?_⟩
    exact hp'.2.2

variable [NeZero N]

/-- `fourierSum` written as an ordinary sum over the source finset. -/
theorem fourierSum_eq_finset_sum (A : Finset (ZMod N)) (d : ZMod N) :
    fourierSum A d = ∑ a ∈ A, ZMod.stdAddChar (a * d) := by
  rw [fourierSum]
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach A (fun a ↦ ZMod.stdAddChar (a * d)))

/-- Multiplication of two mask Fourier sums expands over `A × B`. -/
theorem fourierSum_mul_fourierSum (A B : Finset (ZMod N)) (d : ZMod N) :
    fourierSum A d * fourierSum B d =
      ∑ p ∈ A ×ˢ B, ZMod.stdAddChar ((p.1 + p.2) * d) := by
  rw [fourierSum_eq_finset_sum, fourierSum_eq_finset_sum,
    Finset.sum_mul_sum]
  calc
    (∑ a ∈ A, ∑ b ∈ B,
        ZMod.stdAddChar (a * d) * ZMod.stdAddChar (b * d)) =
        ∑ p ∈ A ×ˢ B,
          ZMod.stdAddChar (p.1 * d) * ZMod.stdAddChar (p.2 * d) := by
      exact (Finset.sum_product A B (fun p ↦
        ZMod.stdAddChar (p.1 * d) * ZMod.stdAddChar (p.2 * d))).symm
    _ = ∑ p ∈ A ×ˢ B, ZMod.stdAddChar ((p.1 + p.2) * d) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring

/-- Orthogonality of all standard characters of `ZMod N`. -/
theorem sum_stdAddChar_mul (z : ZMod N) :
    ∑ d : ZMod N, ZMod.stdAddChar (d * z) =
      if z = 0 then (N : ℂ) else 0 := by
  simpa using AddChar.sum_mulShift z (ZMod.isPrimitive_stdAddChar N)

/-- Exact Fourier inversion identity for the number of representations of
`g` as `a + b`. -/
theorem sum_fourier_product_twist (A B : Finset (ZMod N)) (g : ZMod N) :
    (∑ d : ZMod N,
      fourierSum A d * fourierSum B d * ZMod.stdAddChar (-(g * d))) =
      (N : ℂ) * (representationFinset A B g).card := by
  simp_rw [fourierSum_mul_fourierSum]
  calc
    (∑ d : ZMod N,
        (∑ p ∈ A ×ˢ B, ZMod.stdAddChar ((p.1 + p.2) * d)) *
          ZMod.stdAddChar (-(g * d))) =
        ∑ d : ZMod N, ∑ p ∈ A ×ˢ B,
          ZMod.stdAddChar ((p.1 + p.2) * d) *
            ZMod.stdAddChar (-(g * d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
    _ = ∑ p ∈ A ×ˢ B,
        ∑ d : ZMod N,
          ZMod.stdAddChar ((p.1 + p.2) * d) *
            ZMod.stdAddChar (-(g * d)) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ A ×ˢ B,
          ∑ d : ZMod N,
            ZMod.stdAddChar (d * ((p.1 + p.2) - g)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro d hd
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ p ∈ A ×ˢ B,
          if p.1 + p.2 = g then (N : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [sum_stdAddChar_mul]
      simp only [sub_eq_zero]
    _ = (N : ℂ) * (representationFinset A B g).card := by
      rw [← Finset.sum_filter]
      simp [representationFinset, mul_comm]

/-- A cover of all nonzero frequencies, together with the cardinality
identity, makes every representation fibre a singleton. -/
theorem representation_card_eq_one_of_fourier_zero_cover
    (A B : Finset (ZMod N))
    (hcard : A.card * B.card = N)
    (hcover : ∀ d : ZMod N, d ≠ 0 →
      fourierSum A d = 0 ∨ fourierSum B d = 0) :
    ∀ g, (representationFinset A B g).card = 1 := by
  intro g
  have hsum :
      (∑ d : ZMod N,
        fourierSum A d * fourierSum B d * ZMod.stdAddChar (-(g * d))) =
        (N : ℂ) := by
    calc
      (∑ d : ZMod N,
          fourierSum A d * fourierSum B d *
            ZMod.stdAddChar (-(g * d))) =
          ∑ d : ZMod N, if d = 0 then (N : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hd0 : d = 0
        · subst d
          simp only [fourierSum_zero, mul_zero, neg_zero,
            AddChar.map_zero_eq_one, mul_one, if_pos]
          exact_mod_cast hcard
        · rw [if_neg hd0]
          rcases hcover d hd0 with hA | hB
          · simp [hA]
          · simp [hB]
      _ = (N : ℂ) := by simp
  have hinversion := sum_fourier_product_twist A B g
  rw [hsum] at hinversion
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hcast : ((representationFinset A B g).card : ℂ) = 1 := by
    apply mul_left_cancel₀ hN
    simpa [mul_assoc] using hinversion.symm
  exact_mod_cast hcast

/-- Main reusable bridge: a complete nonzero Fourier-zero cover certifies
that `A` tiles with complement `B`. -/
theorem tiles_of_fourier_zero_cover
    (A B : Finset (ZMod N))
    (hcard : A.card * B.card = N)
    (hcover : ∀ d : ZMod N, d ≠ 0 →
      fourierSum A d = 0 ∨ fourierSum B d = 0) :
    Tiles A B := by
  exact tiles_of_representation_card_eq_one A B
    (representation_card_eq_one_of_fourier_zero_cover A B hcard hcover)

/-- Cyclotomic-certificate form of the same bridge. -/
theorem tiles_of_cyclotomic_zero_cover
    (A B : Finset (ZMod N))
    (hcard : A.card * B.card = N)
    (hcover : ∀ d : ZMod N, d ≠ 0 →
      CyclotomicZero N A d ∨ CyclotomicZero N B d) :
    Tiles A B := by
  apply tiles_of_fourier_zero_cover A B hcard
  intro d hd
  rcases hcover d hd with hA | hB
  · exact Or.inl ((cyclotomicZero_iff_fourierSum_zero A d).1 hA)
  · exact Or.inr ((cyclotomicZero_iff_fourierSum_zero B d).1 hB)

end Fuglede
