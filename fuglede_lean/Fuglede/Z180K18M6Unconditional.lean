import Fuglede.Z180K18M6DPSemantic
import Fuglede.Z180K18M6Terminal

/-! # Unconditional closure of the `k = 18`, `m = 6` branch -/

namespace Fuglede

/-- Unconditional terminal certificate for the `m = 6` branch. -/
theorem z180_k18_terminal_branch_six :
    Z180K18TerminalBranchCertificate 6 :=
  z180_k18_terminal_branch_six_of_envelope z180_k18_m6_envelope

#print axioms z180_k18_terminal_branch_six

end Fuglede
