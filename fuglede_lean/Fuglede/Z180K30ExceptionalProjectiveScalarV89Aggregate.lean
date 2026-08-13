import Fuglede.Z180K30ExceptionalProjectiveScalarV89D3
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6
import Fuglede.Z180K30ExceptionalProjectiveNormalizationFromAuditV89

/-! Complete literal audit over every normalized projective pair. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_normalized_projective_scalar_audit_v89 :
    Z180K30NormalizedProjectiveLiteralAuditV89 := by
  intro divisor hsupported
  rcases hsupported with rfl | rfl | rfl
  · exact ⟨z180_k30_certified_projective_literal_audit_v89_d3⟩
  · exact ⟨z180_k30_certified_projective_literal_audit_v89_d4⟩
  · exact ⟨z180_k30_certified_projective_literal_audit_v89_d6⟩

#print axioms z180_k30_normalized_projective_scalar_audit_v89

theorem z180_k30_exceptional_projective_normalization_v89 :
    Fuglede.Z180K30ExceptionalProjectiveNormalizationV86 :=
  z180_k30_projectiveNormalization_of_normalizedAudit_v89
    z180_k30_normalized_projective_scalar_audit_v89

#print axioms z180_k30_exceptional_projective_normalization_v89

end Fuglede.Z180K30ExceptionalRawV2
