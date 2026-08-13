import Fuglede.Z180K6DefectZeroEnvelope
import Fuglede.Z180K6DescentForceSix

/-!
# Cardinality-six closure reduced exactly to `ZMod 36`

The descent chain proves that a putative non-tiler produces the concrete
`Phi_30`/not-`Phi_6` defect, assuming only the smaller-modulus theorem for
six-point spectral sets in `ZMod 36`.  The independently checked zero sieve
and terminal graph prove that this defect is impossible.

Thus this module exposes the exact induction boundary and nothing else.
-/

namespace Fuglede

/-- Spectral-to-tiling at cardinality six in `ZMod 180`, conditional only on
the corresponding exact theorem in `ZMod 36`. -/
theorem z180_k6_exists_tiling_of_spectral_of_z36_card_six
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hInduction : Z36SpectralCard6ImpliesTile) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_contra hnot
  obtain ⟨h30, h6⟩ :=
    z180_k6_phi30_defect_of_non_tiler
      hSpec hcard hInduction hnot
  exact z180_k6_phi30_defect_impossible_of_spectral
    hSpec hcard h30 h6

#print axioms z180_k6_exists_tiling_of_spectral_of_z36_card_six

end Fuglede
