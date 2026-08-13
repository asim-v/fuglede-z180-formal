import Fuglede.Z180K30ExceptionalProjectiveScalarV89D3U000
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D3U001
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D3U002
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D3

/-! Generated complete literal audit for divisor 3. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralLookupForV89D3 : Nat → Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0, vIndex => z180K30ProjectiveLiteralRowLookupV89D3U000 vIndex
  | 1, vIndex => z180K30ProjectiveLiteralRowLookupV89D3U001 vIndex
  | 2, vIndex => z180K30ProjectiveLiteralRowLookupV89D3U002 vIndex
  | _, _ => []

def z180_k30_certified_projective_literal_audit_v89_d3 :
    CertifiedNormalizedProjectiveLiteralAuditV89 3 where
  uGroups := z180K30ProjectiveLiteralUGroupsV89D3
  vGroups := z180K30ProjectiveLiteralVGroupsV89D3
  lookupFor := z180K30ProjectiveLiteralLookupForV89D3
  uGroups_complete := by decide
  vGroups_complete := by decide
  audited := by
    intro uIndex huIndex vIndex hvIndex
    interval_cases uIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D3] using
        z180_k30_projective_literal_row_audit_v89_d3_u000 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D3] using
        z180_k30_projective_literal_row_audit_v89_d3_u001 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D3] using
        z180_k30_projective_literal_row_audit_v89_d3_u002 vIndex hvIndex

#print axioms z180_k30_certified_projective_literal_audit_v89_d3

end Fuglede.Z180K30ExceptionalRawV2
