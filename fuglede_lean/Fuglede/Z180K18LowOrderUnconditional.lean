import Fuglede.Z180K18M2Phi2Phi18Semantic
import Fuglede.Z180K18M4Phi4HighSemantic
import Fuglede.Z180K18M2NoHighEdgeCertificate
import Fuglede.Z180K18M4NoHighEdgeCertificate

/-!
# Unconditional terminal closure of the `m = 2` and `m = 4` branches

The semantic envelope computations and the finite no-high-edge census
certificates are now all kernel-checked.  This module packages them into the
two corresponding terminal branch certificates without any remaining input.
-/

namespace Fuglede

/-- The fully inhabited low-order audit used by the cardinality-eighteen
terminal reduction. -/
def z180K18LowOrderAudit : Z180K18LowOrderAuditInterface where
  m2Envelope := z180_k18_m2_envelope
  m4Envelope := z180_k18_m4_envelope
  m2NoHighEdge := z180_k18_m2_noHighEdgeCensus
  m4NoHighEdge := z180_k18_m4_noHighEdgeCensus

/-- The `m = 2` and `m = 4` terminal branches, with no external premise. -/
theorem z180_k18_terminal_branches_two_four :
    Z180K18TerminalBranchCertificate 2 /\
      Z180K18TerminalBranchCertificate 4 :=
  z180_k18_terminalBranches_two_four_of_lowOrderAudit
    z180K18LowOrderAudit

#print axioms z180_k18_terminal_branches_two_four

end Fuglede
