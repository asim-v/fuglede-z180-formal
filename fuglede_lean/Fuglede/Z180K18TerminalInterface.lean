import Fuglede.Z180K18DefectCoreReduction

/-!
# Honest terminal interface for the cardinality-eighteen branch

The reproducible external audit closes the remaining descent branches by
exact envelope, clique, profile, forced-zero, and Fourier-cover
certificates.  Those certificates have not yet been reconstructed in Lean.
This module exposes their exact logical boundary as a `Prop`; it introduces
no axiom and asserts no inhabitant.
-/

namespace Fuglede

/-- One exact terminal branch certificate. -/
def Z180K18TerminalBranchCertificate (m : Nat) : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt m A L →
    ∃ B : Finset (ZMod 180), Tiles A B

/-- The sole still-missing terminal boundary after the table-free core
reduction.  The conjunction exposes separately the six retained defect
orders.  In the external audit, the `18` and `36` branches are preflight
exclusions, `6` and `12` are profile exclusions, and `2` and `4` end in the
four explicit Fourier-cover tiling routes. -/
def Z180K18TerminalCertificate : Prop :=
  Z180K18TerminalBranchCertificate 2 ∧
    Z180K18TerminalBranchCertificate 4 ∧
    Z180K18TerminalBranchCertificate 6 ∧
    Z180K18TerminalBranchCertificate 12 ∧
    Z180K18TerminalBranchCertificate 18 ∧
    Z180K18TerminalBranchCertificate 36

end Fuglede
