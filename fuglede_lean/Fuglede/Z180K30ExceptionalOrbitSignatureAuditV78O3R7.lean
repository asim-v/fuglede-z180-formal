import Fuglede.Z180K30ExceptionalOrbitSignatureAuditV78

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180_k30_exceptional_orbit_signature_audit_v78_o3_r7 :
    z180K30OrbitSignatureAuditV78 (3 : Fin 8) (7 : Fin 8) =
      { enumerated := 432, accepted := 432, uncovered := 0 } := by
  decide

#print axioms z180_k30_exceptional_orbit_signature_audit_v78_o3_r7

end Fuglede.Z180K30ExceptionalRawV2

