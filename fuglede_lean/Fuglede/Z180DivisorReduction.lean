import Fuglede.Z180CardinalityEndpoints
import Fuglede.Z180ClosedCases
import Fuglede.Z180DivisorCases

/-!
# Exhaustive reduction of the divisor cardinalities at modulus 180

This theorem is intentionally a reduction rather than a claimed solution.
Assuming the still-unassembled cardinality divisibility statement, every
spectral cardinality is either already covered by an unconditional tiling
endpoint or belongs to the five explicitly named structural cases.
-/

namespace Fuglede

/-- Among positive divisors of `180`, only `6, 10, 12, 18, 30` remain
outside the currently assembled unconditional tiling endpoints. -/
theorem z180_spectral_divisor_reduction
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hdvd : A.card ∣ 180) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 12 ∨
      A.card = 18 ∨ A.card = 30 := by
  by_cases hlarge : 90 < A.card
  · exact Or.inl (z180_exists_tiling_of_spectral_of_ninety_lt_card hSpec hlarge)
  have hle : A.card ≤ 90 := by omega
  have hpos : 0 < A.card := Finset.card_pos.mpr hSpec.1
  rcases dvd_180_cases_of_le_ninety hpos hle hdvd with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))
  · exact Or.inl (z180_exists_tiling_of_spectral_of_closed_cardinality hSpec (by omega))

#print axioms z180_spectral_divisor_reduction

end Fuglede
