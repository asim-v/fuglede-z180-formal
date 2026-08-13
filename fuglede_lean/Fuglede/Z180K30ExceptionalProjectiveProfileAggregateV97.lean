import Fuglede.Z180K30ExceptionalProjectiveProfileDivisorV97D3
import Fuglede.Z180K30ExceptionalProjectiveProfileDivisorV97D4
import Fuglede.Z180K30ExceptionalProjectiveProfileDivisorV97D6
import Fuglede.Z180K30ExceptionalProjectiveScalarNormalizationAdapterV97

/-! Complete V97 profile certificate and the unchanged V89 audit endpoint. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_normalized_projective_profile_audit_v97 :
    Z180K30NormalizedProjectiveProfileAuditV97 := by
  intro divisor hsupported
  rcases hsupported with rfl | rfl | rfl
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D3⟩
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D4⟩
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D6⟩

theorem z180_k30_normalized_projective_scalar_audit_v97 :
    Z180K30NormalizedProjectiveScalarAuditV89 :=
  normalizedProjectiveProfileAudit_to_scalarAudit_v97
    z180_k30_normalized_projective_profile_audit_v97

theorem z180_k30_projective_normalization_v97 :
    Fuglede.Z180K30ExceptionalProjectiveNormalizationV86 :=
  z180_k30_projectiveNormalization_of_scalarAudit_v97
    z180_k30_normalized_projective_scalar_audit_v97

#print axioms z180_k30_normalized_projective_profile_audit_v97
#print axioms z180_k30_normalized_projective_scalar_audit_v97
#print axioms z180_k30_projective_normalization_v97

end Fuglede.Z180K30ExceptionalRawV2
