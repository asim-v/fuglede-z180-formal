import Fuglede.Z180K30ExceptionalAffineCandidateAuditCoreV95

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem z180_k30_affine_candidate_v95_o4_u23
    (translation : RawPoint) :
    z180K30CompatibleAffineCandidateAtB_v95 4 23 translation = true := by
  fin_cases translation <;> decide

#print axioms z180_k30_affine_candidate_v95_o4_u23

end Fuglede.Z180K30ExceptionalRawV2
