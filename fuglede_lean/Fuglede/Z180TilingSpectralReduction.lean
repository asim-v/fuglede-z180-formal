import Fuglede.CardinalityEndpoints
import Fuglede.FourierTiling
import Fuglede.Z180DivisorCases
import Fuglede.ZModDFTSupport
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

/-- The indicator function of a finite subset, with complex values. -/
noncomputable def finsetIndicator (A : Finset (ZMod N)) : ZMod N → ℂ :=
  fun x ↦ if x ∈ A then 1 else 0

/-- The DFT of an indicator is the mask Fourier sum with the opposite sign. -/
theorem dft_finsetIndicator (A : Finset (ZMod N)) (d : ZMod N) :
    ZMod.dft (finsetIndicator A) d = fourierSum A (-d) := by
  classical
  rw [ZMod.dft_apply, fourierSum_eq_finset_sum]
  simp [finsetIndicator]

/-- Fourier coefficients of a real-valued indicator have conjugate symmetry. -/
theorem fourierSum_neg (A : Finset (ZMod N)) (d : ZMod N) :
    fourierSum A (-d) = star (fourierSum A d) := by
  simp only [fourierSum, star_sum]
  apply Fintype.sum_congr
  intro a
  rw [star_stdAddChar]
  congr 1
  ring

/-- Squaring three unit complex numbers preserves a vanishing three-term
sum. -/
theorem unit_triple_square_sum_zero {u v w : ℂ}
    (hu : u * star u = 1) (hv : v * star v = 1)
    (hw : w * star w = 1) (hsum : u + v + w = 0) :
    u ^ 2 + v ^ 2 + w ^ 2 = 0 := by
  have hstar : star u + star v + star w = 0 := by
    have h := congrArg (starRingEnd ℂ) hsum
    simpa using h
  have hpairs : u * v + u * w + v * w = 0 := by
    calc
      u * v + u * w + v * w =
          u * v * (w * star w) + u * w * (v * star v) +
            v * w * (u * star u) := by rw [hu, hv, hw]; ring
      _ = u * v * w * (star u + star v + star w) := by ring
      _ = 0 := by rw [hstar, mul_zero]
  calc
    u ^ 2 + v ^ 2 + w ^ 2 =
        (u + v + w) ^ 2 - 2 * (u * v + u * w + v * w) := by ring
    _ = 0 := by rw [hsum, hpairs]; norm_num

theorem stdAddChar_mul_star_self (x : ZMod N) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

/-- For a three-point set, one Fourier zero forces the doubled frequency to
vanish as well. -/
theorem fourierSum_add_self_eq_zero_of_card_three
    {A : Finset (ZMod N)} {d : ZMod N} (hcard : A.card = 3)
    (hzero : fourierSum A d = 0) :
    fourierSum A (d + d) = 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [fourierSum_eq_finset_sum] at hzero ⊢
  have hsum :
      ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) +
        ZMod.stdAddChar (c * d) = 0 := by
    simpa [hab, hac, hbc, add_assoc] using hzero
  have hsquares := unit_triple_square_sum_zero
    (stdAddChar_mul_star_self (a * d))
    (stdAddChar_mul_star_self (b * d))
    (stdAddChar_mul_star_self (c * d)) hsum
  have hpow (x : ZMod N) :
      ZMod.stdAddChar (x * (d + d)) = ZMod.stdAddChar (x * d) ^ 2 := by
    rw [pow_two, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simpa [hab, hac, hbc, add_assoc, hpow] using hsquares

/-- If all nonzero Fourier coefficients of a nonempty indicator vanish, the
set is the whole cyclic group. -/
theorem eq_univ_of_fourierSum_eq_zero_off_zero
    {A : Finset (ZMod N)} (hA : A.Nonempty)
    (hzero : ∀ d : ZMod N, d ≠ 0 → fourierSum A d = 0) :
    A = Finset.univ := by
  have hdft : ∀ d : ZMod N, d ≠ 0 → ZMod.dft (finsetIndicator A) d = 0 := by
    intro d hd
    rw [dft_finsetIndicator]
    apply hzero (-d)
    simpa using hd
  have hconstant := eq_of_dft_eq_zero_off_zero (finsetIndicator A) hdft
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨x, hx⟩ := hA
  have hxy := hconstant x y
  by_contra hy
  simp [finsetIndicator, hx, hy] at hxy

/-- If the second factor of a tiling is nonempty and proper, then the first
factor has a nonzero Fourier zero. -/
theorem exists_nonzero_fourier_zero_left_of_tiles
    {A B : Finset (ZMod N)} (hTiles : Tiles A B)
    (hB : B.Nonempty) (hBproper : B ≠ Finset.univ) :
    ∃ d : ZMod N, d ≠ 0 ∧ fourierSum A d = 0 := by
  by_contra hnone
  push Not at hnone
  have hBzero : ∀ d : ZMod N, d ≠ 0 → fourierSum B d = 0 := by
    intro d hd
    exact (fourier_zero_cover_of_tiles hTiles d hd).resolve_left (hnone d hd)
  exact hBproper (eq_univ_of_fourierSum_eq_zero_off_zero hB hBzero)

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

/-- Every two-point tile in `ZMod 180` has an exact two-point spectrum. -/
theorem z180_exists_spectrum_of_tile_card_two
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 2) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 90 := by omega
  have hBpos : 0 < B.card := by omega
  have hB : B.Nonempty := Finset.card_pos.mp hBpos
  have hBproper : B ≠ Finset.univ := by
    intro h
    subst B
    simp at hBcard
  obtain ⟨d, hd, hzero⟩ :=
    exists_nonzero_fourier_zero_left_of_tiles hTiles hB hBproper
  refine ⟨{0, d}, (cyclotomicSpectrum_iff_fourierSpectrum A {0, d}).2 ?_⟩
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · have h0d : (0 : ZMod 180) ≠ d := Ne.symm hd
    simpa [h0d] using hcard
  · intro l₁ hl₁ l₂ hl₂ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl₁ hl₂
    rcases hl₁ with rfl | rfl <;> rcases hl₂ with rfl | rfl
    · exact (hne rfl).elim
    · rw [zero_sub, fourierSum_neg, hzero, star_zero]
    · simpa using hzero
    · exact (hne rfl).elim

/-- Every three-point tile in `ZMod 180` has an exact three-point spectrum. -/
theorem z180_exists_spectrum_of_tile_card_three
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 3) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 60 := by omega
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hBproper : B ≠ Finset.univ := by
    intro h
    subst B
    simp at hBcard
  obtain ⟨d, hd, hzero⟩ :=
    exists_nonzero_fourier_zero_left_of_tiles hTiles hB hBproper
  have hneg : fourierSum A (-d) = 0 := by
    rw [fourierSum_neg, hzero, star_zero]
  have hdouble : fourierSum A (d + d) = 0 :=
    fourierSum_add_self_eq_zero_of_card_three hcard hzero
  have hdoubleNeg : fourierSum A (-(d + d)) = 0 := by
    rw [fourierSum_neg, hdouble, star_zero]
  have hdneg : d ≠ -d := by
    intro heq
    have htwo : d + d = 0 := (eq_neg_iff_add_eq_zero.mp heq)
    rw [htwo, fourierSum_zero, hcard] at hdouble
    norm_num at hdouble
  have h0d : (0 : ZMod 180) ≠ d := Ne.symm hd
  have h0negd : (0 : ZMod 180) ≠ -d := by simpa using hd
  refine ⟨{0, d, -d},
    (cyclotomicSpectrum_iff_fourierSpectrum A {0, d, -d}).2 ?_⟩
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · simpa [h0d, h0negd, hdneg] using hcard
  · intro l₁ hl₁ l₂ hl₂ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl₁ hl₂
    rcases hl₁ with rfl | rfl | rfl <;>
      rcases hl₂ with rfl | rfl | rfl
    · exact (hne rfl).elim
    · simpa using hneg
    · simpa using hzero
    · simpa using hzero
    · exact (hne rfl).elim
    · convert hdouble using 1 <;> ring
    · simpa using hneg
    · convert hdoubleNeg using 1 <;> ring
    · exact (hne rfl).elim

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

/-- Honest endpoint reduction for the converse: sizes one, two, three, and 180
are spectral; every unresolved tile has one of the fourteen remaining divisor
cardinalities. -/
theorem z180_tiling_to_spectral_cardinality_reduction
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 4 ∨ A.card = 5 ∨ A.card = 6 ∨ A.card = 9 ∨
      A.card = 10 ∨ A.card = 12 ∨
      A.card = 15 ∨ A.card = 18 ∨ A.card = 20 ∨ A.card = 30 ∨
      A.card = 36 ∨ A.card = 45 ∨ A.card = 60 ∨ A.card = 90 := by
  rcases z180_tile_card_cases hTiles with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inl h))
  · exact Or.inl (z180_exists_spectrum_of_tile_card_two hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_three hTiles h)
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inr h))

#print axioms z180_tiling_to_spectral_cardinality_reduction

end Fuglede
