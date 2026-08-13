import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B014
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D6

/-! Generated row aggregate for divisor 6, U group 14. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralRowLookupV89D6U014 : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0 => z180K30ProjectiveScalarV89D6B014Lookups
  | _ => []

theorem z180_k30_projective_literal_row_audit_v89_d6_u014
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D6.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D6.getD 14 [])
      (z180K30ProjectiveLiteralVGroupsV89D6.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 6
          (z180K30ProjectiveLiteralRowLookupV89D6U014 vIndex)) = true := by
  interval_cases vIndex
  · rw [z180K30ProjectiveLiteralUGroupV89D6G014,
      z180K30ProjectiveLiteralVGroupV89D6G000,
      ← z180K30ProjectiveScalarV89D6B014Pairs_eq]
    simpa [z180K30ProjectiveLiteralRowLookupV89D6U014] using
      z180K30ProjectiveScalarV89D6B014Audit

#print axioms z180_k30_projective_literal_row_audit_v89_d6_u014

end Fuglede.Z180K30ExceptionalRawV2
