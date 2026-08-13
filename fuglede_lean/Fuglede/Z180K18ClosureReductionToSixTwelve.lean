import Fuglede.Z180K18ConditionalClosure
import Fuglede.Z180K18TerminalReductionToSixTwelve

/-!
# Cardinality-eighteen closure reduced to the `m = 6, 12` branches
-/

namespace Fuglede

/-- A spectral set of cardinality eighteen tiles once the two remaining
terminal branches (`m = 6` and `m = 12`) are supplied. -/
theorem z180_k18_exists_tiling_of_spectral_of_six_twelve
    (h6 : Z180K18TerminalBranchCertificate 6)
    (h12 : Z180K18TerminalBranchCertificate 12)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18) :
    ∃ B : Finset (ZMod 180), Tiles A B :=
  z180_k18_exists_tiling_of_spectral_of_terminalCertificate
    (z180_k18_terminalCertificate_of_six_twelve h6 h12)
    hSpec hcard

#print axioms z180_k18_exists_tiling_of_spectral_of_six_twelve

end Fuglede
