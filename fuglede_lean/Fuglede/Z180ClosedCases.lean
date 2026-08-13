import Fuglede.Z180K4Closure
import Fuglede.Z180K5Closure
import Fuglede.Z180K9Closure
import Fuglede.Z180K15Closure
import Fuglede.Z180ProjectionTiles
import Fuglede.Z180PrimePowerFibers
import Fuglede.Z180SmallCardinality
import Fuglede.Z180TrivialCardinalities

/-!
# Assembled unconditional cardinality cases at modulus 180

This theorem is deliberately an explicit disjunction.  It records only cases
whose spectral-to-tiling endpoint has already been reconstructed by Lean, and
therefore cannot silently turn a computational or conditional case into a
proved one.
-/

namespace Fuglede

theorem z180_exists_tiling_of_spectral_of_closed_cardinality
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard :
      A.card = 1 ∨ A.card = 2 ∨ A.card = 3 ∨ A.card = 4 ∨
      A.card = 5 ∨ A.card = 9 ∨ A.card = 15 ∨ A.card = 20 ∨ A.card = 36 ∨
      A.card = 45 ∨ A.card = 60 ∨ A.card = 90 ∨ A.card = 180) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  rcases hcard with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact z180_exists_tiling_of_card_one h
  · exact z180_spectral_card_two_tiles hSpec h
  · exact z180_spectral_card_three_tiles hSpec h
  · exact z180_k4_exists_tiling_of_spectral hSpec h
  · exact z180_k5_exists_tiling_of_spectral hSpec h
  · exact z180_k9_exists_tiling_of_spectral hSpec h
  · exact z180_k15_exists_tiling_of_spectral hSpec h
  · exact z180_exists_tiling_of_spectral_card_twenty hSpec h
  · exact z180_exists_tiling_of_spectral_card_thirty_six hSpec h
  · exact z180_exists_tiling_of_spectral_card_forty_five hSpec h
  · exact z180_exists_tiling_of_spectral_card_sixty hSpec h
  · exact z180_exists_tiling_of_spectral_card_ninety hSpec h
  · exact z180_exists_tiling_of_spectral_card_one_eighty hSpec h

#print axioms z180_exists_tiling_of_spectral_of_closed_cardinality

end Fuglede
