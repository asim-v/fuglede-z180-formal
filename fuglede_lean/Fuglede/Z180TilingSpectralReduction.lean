import Fuglede.CardinalityEndpoints
import Fuglede.FourierTiling
import Fuglede.Z180DivisorCases
import Mathlib.Tactic

/-!
# First reduction for tiling implies spectrality in `ZMod 180`

The Fourier identity in `FourierTiling` supplies the exact zero partition of
any tiling pair.  This file records the complementary arithmetic reduction:
the cardinality of a tile is a positive divisor of `180`.  The singleton and
full-group endpoints are already spectral, so only the sixteen explicitly
listed nontrivial divisor sizes remain.
-/

namespace Fuglede

variable {N : ℕ}

/-- A singleton is spectral, with any singleton frequency set. -/
theorem cyclotomicSpectrum_singleton (a l : ZMod N) :
    CyclotomicSpectrum N {a} {l} := by
  simp [CyclotomicSpectrum]

variable [NeZero N]

/-- The whole cyclic group is spectral with itself as spectrum. -/
theorem fourierSpectrum_univ :
    FourierSpectrum (Finset.univ : Finset (ZMod N)) Finset.univ := by
  refine ⟨by simp, rfl, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hne
  have hdiff : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [fourierSum_eq_finset_sum]
  simpa [hdiff] using sum_stdAddChar_mul (N := N) (l₁ - l₂)

theorem cyclotomicSpectrum_univ :
    CyclotomicSpectrum N (Finset.univ : Finset (ZMod N)) Finset.univ := by
  exact (cyclotomicSpectrum_iff_fourierSpectrum
    (Finset.univ : Finset (ZMod N)) Finset.univ).2 fourierSpectrum_univ

/-- The two endpoint cardinalities in `ZMod 180` satisfy the converse. -/
theorem z180_exists_spectrum_of_tile_card_one_or_full
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 1 ∨ A.card = 180) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  rcases hcard with hcard | hcard
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨{0}, cyclotomicSpectrum_singleton a 0⟩
  · have hA : A = Finset.univ := by
      apply full_cardinality_eq_univ
      simpa using hcard
    subst A
    exact ⟨Finset.univ, cyclotomicSpectrum_univ⟩

/-- Every tiling cardinality in `ZMod 180` is one of the eighteen positive
divisors of `180`. -/
theorem z180_tile_card_cases {A B : Finset (ZMod 180)}
    (hTiles : Tiles A B) :
    A.card = 1 ∨ A.card = 2 ∨ A.card = 3 ∨ A.card = 4 ∨
    A.card = 5 ∨ A.card = 6 ∨ A.card = 9 ∨ A.card = 10 ∨
    A.card = 12 ∨ A.card = 15 ∨ A.card = 18 ∨ A.card = 20 ∨
    A.card = 30 ∨ A.card = 36 ∨ A.card = 45 ∨ A.card = 60 ∨
    A.card = 90 ∨ A.card = 180 := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  have hpos : 0 < A.card := by
    by_contra h
    have hzero : A.card = 0 := by omega
    rw [hzero, zero_mul] at hprod
    omega
  exact dvd_180_cases hpos (card_dvd_modulus_of_tiles_left hTiles)

/-- Honest endpoint reduction for the converse: endpoint tiles are already
spectral; every unresolved tile has one of the sixteen remaining divisor
cardinalities. -/
theorem z180_tiling_to_spectral_cardinality_reduction
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 2 ∨ A.card = 3 ∨ A.card = 4 ∨ A.card = 5 ∨
      A.card = 6 ∨ A.card = 9 ∨ A.card = 10 ∨ A.card = 12 ∨
      A.card = 15 ∨ A.card = 18 ∨ A.card = 20 ∨ A.card = 30 ∨
      A.card = 36 ∨ A.card = 45 ∨ A.card = 60 ∨ A.card = 90 := by
  rcases z180_tile_card_cases hTiles with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inr h))

#print axioms z180_tiling_to_spectral_cardinality_reduction

end Fuglede
