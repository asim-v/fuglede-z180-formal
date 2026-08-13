import Fuglede.Z180K15TwoBranchReduction
import Fuglede.Z180K15Phi15Branch
import Fuglede.Z180K15Phi45Branch

/-!
# Unconditional closure of the cardinality-fifteen branch in `ZMod 180`

The characteristic-two obstruction reduces the problem to a projected
factor failure.  The `Phi_3`, `Phi_9`, `Phi_15`, and `Phi_45` branches each
give an explicit tiling of the image in `ZMod 45`; the sealed order-five
gateway excludes `Phi_5`.  Every image tiling lifts through the injective
projection from `ZMod 180`.
-/

namespace Fuglede

/-- Every cardinality-fifteen cyclotomic spectral set in `ZMod 180` tiles. -/
theorem z180_k15_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  rcases z180_k15_tiling_or_phi15_or_phi45_projection_failure hSpec hcard with
    htile | hnot15 | hnot45
  · exact htile
  · exact z180_k15_exists_tiling_of_not_phi15_dvd_projection45_spectrum_mask
      hSpec hcard hnot15
  · exact z180_k15_exists_tiling_of_not_phi45_dvd_projection45_spectrum_mask
      hSpec hcard hnot45

#print axioms z180_k15_exists_tiling_of_spectral

end Fuglede
