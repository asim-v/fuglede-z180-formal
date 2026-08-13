import Fuglede.Z180K18M6Unconditional
import Fuglede.Z180K18M12Unconditional
import Fuglede.Z180K18ClosureReductionToSixTwelve

/-! # Unconditional cardinality-eighteen spectral-to-tiling closure -/

namespace Fuglede

/-- The complete terminal certificate at cardinality eighteen. -/
theorem z180_k18_terminalCertificate : Z180K18TerminalCertificate :=
  z180_k18_terminalCertificate_of_six_twelve
    z180_k18_terminal_branch_six z180_k18_terminal_branch_twelve

/-- Every cardinality-eighteen spectral set in `ZMod 180` tiles. -/
theorem z180_k18_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    ∃ B : Finset (ZMod 180), Tiles A B :=
  z180_k18_exists_tiling_of_spectral_of_six_twelve
    z180_k18_terminal_branch_six z180_k18_terminal_branch_twelve
    hSpec hcard

#print axioms z180_k18_terminalCertificate
#print axioms z180_k18_exists_tiling_of_spectral

end Fuglede
