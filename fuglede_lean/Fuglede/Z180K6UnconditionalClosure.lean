import Fuglede.Z36Card6ForcingClosure
import Fuglede.Z180K6ConditionalClosure

/-!
# Unconditional cardinality-six spectral-to-tiling closure in `ZMod 180`

The six-point theorem in `ZMod 36` supplies the sole induction premise of
the already checked descent and defect argument in `ZMod 180`.
-/

namespace Fuglede

/-- Every spectral six-point subset of `ZMod 180` tiles. -/
theorem z180_k6_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    ∃ B : Finset (ZMod 180), Tiles A B :=
  z180_k6_exists_tiling_of_spectral_of_z36_card_six
    hSpec hcard z36_spectral_card6_implies_tile

#print axioms z180_k6_exists_tiling_of_spectral

end Fuglede
