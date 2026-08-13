import Fuglede.Z180K18M12DPSemantic
import Fuglede.Z180K18M12Phi45Semantic
import Fuglede.Z180K18CliqueCensusCertificates

/-!
# Unconditional closure of the `k = 18`, `m = 12` branch

The four paired-remainder families and the structural `q = 45` argument
inhabit the exact mask-zero envelope.  The kernel-checked clique-profile
certificate then turns that envelope into the terminal branch certificate.
-/

namespace Fuglede

/-- The complete set-side envelope in the base-order-twelve defect branch. -/
theorem z180_k18_m12_envelope : Z180K18M12EnvelopeInterface :=
  z180_k18_m12_envelope_of_dp_phi45
    z180_k18_m12_dp z180_k18_m12_phi45_envelope

/-- The exact finite audit with both its semantic envelope and its inhabited
clique-census component. -/
def z180K18M12DefectProfileAudit :
    Z180K18M12DefectProfileAuditInterface :=
  z180K18M12DefectProfileAudit_of_envelope z180_k18_m12_envelope

/-- Unconditional terminal certificate for the `m = 12` branch. -/
theorem z180_k18_terminal_branch_twelve :
    Z180K18TerminalBranchCertificate 12 :=
  z180_k18_terminal_branch_twelve_of_envelope z180_k18_m12_envelope

#print axioms z180_k18_m12_envelope
#print axioms z180_k18_terminal_branch_twelve

end Fuglede
