import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U000
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U001
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U002
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U003
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U004
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U005
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U006
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U007
import Fuglede.Z180K30ExceptionalProjectiveScalarV89D4U008
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D4

/-! Generated complete literal audit for divisor 4. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralLookupForV89D4 : Nat → Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U000 vIndex
  | 1, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U001 vIndex
  | 2, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U002 vIndex
  | 3, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U003 vIndex
  | 4, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U004 vIndex
  | 5, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U005 vIndex
  | 6, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U006 vIndex
  | 7, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U007 vIndex
  | 8, vIndex => z180K30ProjectiveLiteralRowLookupV89D4U008 vIndex
  | _, _ => []

def z180_k30_certified_projective_literal_audit_v89_d4 :
    CertifiedNormalizedProjectiveLiteralAuditV89 4 where
  uGroups := z180K30ProjectiveLiteralUGroupsV89D4
  vGroups := z180K30ProjectiveLiteralVGroupsV89D4
  lookupFor := z180K30ProjectiveLiteralLookupForV89D4
  uGroups_complete := by decide
  vGroups_complete := by decide
  audited := by
    intro uIndex huIndex vIndex hvIndex
    interval_cases uIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u000 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u001 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u002 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u003 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u004 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u005 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u006 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u007 vIndex hvIndex
    · simpa [z180K30ProjectiveLiteralLookupForV89D4] using
        z180_k30_projective_literal_row_audit_v89_d4_u008 vIndex hvIndex

#print axioms z180_k30_certified_projective_literal_audit_v89_d4

end Fuglede.Z180K30ExceptionalRawV2
