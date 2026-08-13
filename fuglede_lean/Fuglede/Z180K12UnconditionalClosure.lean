import Fuglede.Z180K12DescentForceSix
import Fuglede.Z180K12M6ExactZeroSieveClosure

/-! # Unconditional cardinality-twelve spectral-to-tiling closure in `ZMod 180` -/

namespace Fuglede

/-- Every cardinality-twelve spectral set in `ZMod 180` tiles. -/
theorem z180_k12_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12) :
    ∃ B : Finset (ZMod 180), Tiles A B :=
  z180_k12_exists_tiling_of_spectral_of_reduction_and_exactSieve
    hSpec hcard
    (z180_k12_nonTilerM6Reduction_of_spectral hSpec hcard)
    z180_k12_m6_exact_zero_sieve

#print axioms z180_k12_exists_tiling_of_spectral

end Fuglede
