import Fuglede.Z180K18TerminalInterface
import Fuglede.Z36Card18PrimePowerFibers

/-!
# Conditional assembly of the cardinality-eighteen branch in `ZMod 180`

Everything except `Z180K18TerminalCertificate` is supplied by kernel-checked
or separately generated modules.  In particular, the theorem below does not
promote the external terminal audit to a Lean theorem.
-/

namespace Fuglede

/-- The forced `Phi_3`/`Phi_9` core and the five-factor descent connect to the
remaining terminal certificate with no additional hypothesis. -/
theorem z180_k18_exists_tiling_of_spectral_of_terminalCertificate
    (hterminal : Z180K18TerminalCertificate)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_contra hnot
  have hdefect := z180_k18_fiveFactorDefect_of_non_tiler
    hSpec hcard z36_spectral_card18_implies_tile hnot
  have hreduced :=
    z180_k18_reducedFiveFactorDefect_of_fiveFactorDefect
      hSpec hcard hdefect
  have hcore := z180_k18_corePhi3Phi9Zeros_of_spectral hSpec hcard
  rcases hreduced with h2 | h4 | h6 | h12 | h18 | h36
  · exact hnot (hterminal.1 A L hSpec hcard hcore h2)
  · exact hnot (hterminal.2.1 A L hSpec hcard hcore h4)
  · exact hnot (hterminal.2.2.1 A L hSpec hcard hcore h6)
  · exact hnot (hterminal.2.2.2.1 A L hSpec hcard hcore h12)
  · exact hnot (hterminal.2.2.2.2.1 A L hSpec hcard hcore h18)
  · exact hnot (hterminal.2.2.2.2.2 A L hSpec hcard hcore h36)

#print axioms z180_k18_exists_tiling_of_spectral_of_terminalCertificate

end Fuglede
