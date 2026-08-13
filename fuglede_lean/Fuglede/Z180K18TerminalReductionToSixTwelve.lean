import Fuglede.Z180K18LowOrderUnconditional
import Fuglede.Z180K18TerminalHighOrder

/-!
# Reduction of the cardinality-eighteen terminal boundary to `m = 6, 12`

The branches `2`, `4`, `18`, and `36` are unconditional.  Hence the complete
terminal certificate needs only certificates for the two remaining orders.
-/

namespace Fuglede

/-- Assemble the exact terminal certificate from only its `m = 6` and
`m = 12` branches. -/
theorem z180_k18_terminalCertificate_of_six_twelve
    (h6 : Z180K18TerminalBranchCertificate 6)
    (h12 : Z180K18TerminalBranchCertificate 12) :
    Z180K18TerminalCertificate := by
  rcases z180_k18_terminal_branches_two_four with ⟨h2, h4⟩
  rcases z180_k18_terminal_high_order_branches with ⟨h18, h36⟩
  exact ⟨h2, h4, h6, h12, h18, h36⟩

#print axioms z180_k18_terminalCertificate_of_six_twelve

end Fuglede
