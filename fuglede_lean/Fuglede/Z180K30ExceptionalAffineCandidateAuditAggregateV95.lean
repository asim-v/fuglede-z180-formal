import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U01
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U05
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U07
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U11
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U13
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U17
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U19
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U23
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U25
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U29
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U31
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O0U35
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U01
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U05
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U07
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U11
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U13
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U17
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U19
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U23
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U25
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U29
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U31
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O2U35
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U01
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U05
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U07
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U11
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U13
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U17
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U19
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U23
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U25
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U29
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U31
import Fuglede.Z180K30ExceptionalAffineCandidateAuditV95O4U35

/-! # Aggregate the 36 fixed-unit affine-candidate certificates. -/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem z180K30AffineCandidateGroupV95O0
    (unit translation : RawPoint) (hunit : unit ∈ units36) :
    z180K30CompatibleAffineCandidateAtB_v95 0 unit translation = true := by
  fin_cases unit <;> simp [units36] at hunit <;>
    first
    | exact z180_k30_affine_candidate_v95_o0_u01 translation
    | exact z180_k30_affine_candidate_v95_o0_u05 translation
    | exact z180_k30_affine_candidate_v95_o0_u07 translation
    | exact z180_k30_affine_candidate_v95_o0_u11 translation
    | exact z180_k30_affine_candidate_v95_o0_u13 translation
    | exact z180_k30_affine_candidate_v95_o0_u17 translation
    | exact z180_k30_affine_candidate_v95_o0_u19 translation
    | exact z180_k30_affine_candidate_v95_o0_u23 translation
    | exact z180_k30_affine_candidate_v95_o0_u25 translation
    | exact z180_k30_affine_candidate_v95_o0_u29 translation
    | exact z180_k30_affine_candidate_v95_o0_u31 translation
    | exact z180_k30_affine_candidate_v95_o0_u35 translation

private theorem z180K30AffineCandidateGroupV95O2
    (unit translation : RawPoint) (hunit : unit ∈ units36) :
    z180K30CompatibleAffineCandidateAtB_v95 2 unit translation = true := by
  fin_cases unit <;> simp [units36] at hunit <;>
    first
    | exact z180_k30_affine_candidate_v95_o2_u01 translation
    | exact z180_k30_affine_candidate_v95_o2_u05 translation
    | exact z180_k30_affine_candidate_v95_o2_u07 translation
    | exact z180_k30_affine_candidate_v95_o2_u11 translation
    | exact z180_k30_affine_candidate_v95_o2_u13 translation
    | exact z180_k30_affine_candidate_v95_o2_u17 translation
    | exact z180_k30_affine_candidate_v95_o2_u19 translation
    | exact z180_k30_affine_candidate_v95_o2_u23 translation
    | exact z180_k30_affine_candidate_v95_o2_u25 translation
    | exact z180_k30_affine_candidate_v95_o2_u29 translation
    | exact z180_k30_affine_candidate_v95_o2_u31 translation
    | exact z180_k30_affine_candidate_v95_o2_u35 translation

private theorem z180K30AffineCandidateGroupV95O4
    (unit translation : RawPoint) (hunit : unit ∈ units36) :
    z180K30CompatibleAffineCandidateAtB_v95 4 unit translation = true := by
  fin_cases unit <;> simp [units36] at hunit <;>
    first
    | exact z180_k30_affine_candidate_v95_o4_u01 translation
    | exact z180_k30_affine_candidate_v95_o4_u05 translation
    | exact z180_k30_affine_candidate_v95_o4_u07 translation
    | exact z180_k30_affine_candidate_v95_o4_u11 translation
    | exact z180_k30_affine_candidate_v95_o4_u13 translation
    | exact z180_k30_affine_candidate_v95_o4_u17 translation
    | exact z180_k30_affine_candidate_v95_o4_u19 translation
    | exact z180_k30_affine_candidate_v95_o4_u23 translation
    | exact z180_k30_affine_candidate_v95_o4_u25 translation
    | exact z180_k30_affine_candidate_v95_o4_u29 translation
    | exact z180_k30_affine_candidate_v95_o4_u31 translation
    | exact z180_k30_affine_candidate_v95_o4_u35 translation

theorem z180K30CompatibleAffineCandidateAtB_true_v95
    (o : Fin 7) (unit translation : RawPoint)
    (hunit : unit ∈ units36) :
    z180K30CompatibleAffineCandidateAtB_v95 o unit translation = true := by
  fin_cases o
  · exact z180K30AffineCandidateGroupV95O0 unit translation hunit
  · simpa [z180K30CompatibleAffineCandidateAtB_v95,
      z180K30NonHOrbitV78Fix2, z180K30CompatibleRowOrbitV78Fix2,
      z180K30ExceptionalOrbitChoicesV4] using
      z180K30AffineCandidateGroupV95O0 unit translation hunit
  · exact z180K30AffineCandidateGroupV95O2 unit translation hunit
  · simpa [z180K30CompatibleAffineCandidateAtB_v95,
      z180K30NonHOrbitV78Fix2, z180K30CompatibleRowOrbitV78Fix2,
      z180K30ExceptionalOrbitChoicesV4] using
      z180K30AffineCandidateGroupV95O0 unit translation hunit
  · exact z180K30AffineCandidateGroupV95O4 unit translation hunit
  · simpa [z180K30CompatibleAffineCandidateAtB_v95,
      z180K30NonHOrbitV78Fix2, z180K30CompatibleRowOrbitV78Fix2,
      z180K30ExceptionalOrbitChoicesV4] using
      z180K30AffineCandidateGroupV95O0 unit translation hunit
  · simpa [z180K30CompatibleAffineCandidateAtB_v95,
      z180K30NonHOrbitV78Fix2, z180K30CompatibleRowOrbitV78Fix2,
      z180K30ExceptionalOrbitChoicesV4] using
      z180K30AffineCandidateGroupV95O0 unit translation hunit

theorem z180K30CompatibleAffineCandidate_of_unit_v95
    (o : Fin 7) (unit translation : RawPoint)
    (hunit : unit ∈ units36) :
    Z180K30CompatibleAffineCandidateAtV95 o unit translation :=
  z180K30CompatibleAffineCandidateAtB_semantics_v95
    o unit translation
    (z180K30CompatibleAffineCandidateAtB_true_v95
      o unit translation hunit)

#print axioms z180K30CompatibleAffineCandidate_of_unit_v95

end Fuglede.Z180K30ExceptionalRawV2
