import Fuglede.Z180CardinalitySieve
import Fuglede.Z180DivisorReduction
import Fuglede.Z180NondivisorClosure
import Fuglede.Z180NondivisorK7Closure
import Fuglede.Z180NondivisorK13Closure
import Fuglede.Z180NondivisorK17Closure
import Fuglede.Z180NondivisorK19Closure
import Fuglede.Z180NondivisorK21Closure
import Fuglede.Z180NondivisorK27Closure

/-!
# Current exhaustive spectral-to-tiling reduction at modulus 180

This module combines the upper-half endpoint, the elementary cardinality
sieve, all presently closed divisor cases, and the kernel-checked exclusions
of cardinalities `7`, `8`, `11`, `13`, `14`, `16`, `17`, `19`, `21`, and
`27`.  It deliberately states a reduction, not a solution: the seven displayed cardinalities are the exact remaining
frontier represented by the imported theorems.
-/

namespace Fuglede

/-- Every spectral subset of `ZMod 180` tiles, unless its cardinality is one
of the five unresolved divisor sizes or one of the two unresolved exceptional
nondivisor sizes. -/
theorem z180_spectral_master_reduction
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 12 ∨
      A.card = 18 ∨ A.card = 30 ∨
      A.card = 24 ∨ A.card = 33 := by
  by_cases hlarge : 90 < A.card
  · exact Or.inl (z180_exists_tiling_of_spectral_of_ninety_lt_card hSpec hlarge)
  have hle : A.card ≤ 90 := by omega
  rcases z180_spectral_cardinality_sieve hSpec hle with
    hdvd | h7 | h8 | h11 | h13 | h14 | h16 | h17 | h19 | h21 | h24 | h27 | h33
  · rcases z180_spectral_divisor_reduction hSpec hdvd with
      htiles | h6 | h10 | h12 | h18 | h30
    · exact Or.inl htiles
    · right; omega
    · right; omega
    · right; omega
    · right; omega
    · right; omega
  · exact (z180_nondivisor_k7_card_ne_of_spectral hSpec h7).elim
  · exact (z180_nondivisor_k8_card_ne_of_spectral hSpec h8).elim
  · exact (z180_nondivisor_k11_card_ne_of_spectral hSpec h11).elim
  · exact (z180_nondivisor_k13_card_ne_of_spectral hSpec h13).elim
  · exact (z180_nondivisor_k14_card_ne_of_spectral hSpec h14).elim
  · exact (z180_nondivisor_k16_card_ne_of_spectral hSpec h16).elim
  · exact (z180_nondivisor_k17_card_ne_of_spectral hSpec h17).elim
  · exact (z180_nondivisor_k19_card_ne_of_spectral hSpec h19).elim
  · exact (z180_nondivisor_k21_card_ne_of_spectral hSpec h21).elim
  · right; omega
  · exact (z180_nondivisor_k27_card_ne_of_spectral hSpec h27).elim
  · right; omega

#print axioms z180_spectral_master_reduction

end Fuglede
