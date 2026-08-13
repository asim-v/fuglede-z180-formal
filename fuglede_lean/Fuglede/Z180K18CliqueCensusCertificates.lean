import Fuglede.Z180K18M2NoHighEdgeCertificate
import Fuglede.Z180K18M4NoHighEdgeCertificate
import Fuglede.Z180K18M12CliqueProfileCertificate

/-!
# Assembly of the inhabited `k = 18` clique censuses

The three graph-theoretic census fields are now kernel-checked.  Consequently
the only remaining hypotheses in these branches are the semantic
mask-zero-envelope computations; no clique/profile interface remains open.
-/

namespace Fuglede

/-- Fill the two low-order census fields from their kernel certificates. -/
def z180K18LowOrderAudit_of_envelopes
    (hm2 : Z180K18M2EnvelopeInterface)
    (hm4 : Z180K18M4EnvelopeInterface) :
    Z180K18LowOrderAuditInterface where
  m2Envelope := hm2
  m4Envelope := hm4
  m2NoHighEdge := z180_k18_m2_noHighEdgeCensus
  m4NoHighEdge := z180_k18_m4_noHighEdgeCensus

/-- Once the two envelope computations are supplied, the order-two and
order-four terminal branches are closed. -/
theorem z180_k18_terminalBranches_two_four_of_envelopes
    (hm2 : Z180K18M2EnvelopeInterface)
    (hm4 : Z180K18M4EnvelopeInterface) :
    Z180K18TerminalBranchCertificate 2 ∧
      Z180K18TerminalBranchCertificate 4 :=
  z180_k18_terminalBranches_two_four_of_lowOrderAudit
    (z180K18LowOrderAudit_of_envelopes hm2 hm4)

/-- Fill the `m = 12` clique-profile field from its kernel certificate. -/
def z180K18M12DefectProfileAudit_of_envelope
    (henvelope : Z180K18M12EnvelopeInterface) :
    Z180K18M12DefectProfileAuditInterface where
  envelope := henvelope
  cliqueCensus := z180_k18_m12_cliqueCensus

/-- The order-twelve terminal branch now depends only on envelope
completeness. -/
theorem z180_k18_terminal_branch_twelve_of_envelope
    (henvelope : Z180K18M12EnvelopeInterface) :
    Z180K18TerminalBranchCertificate 12 :=
  z180_k18_terminal_branch_twelve_of_defectProfileAudit
    (z180K18M12DefectProfileAudit_of_envelope henvelope)

#print axioms z180_k18_terminalBranches_two_four_of_envelopes
#print axioms z180_k18_terminal_branch_twelve_of_envelope

end Fuglede
