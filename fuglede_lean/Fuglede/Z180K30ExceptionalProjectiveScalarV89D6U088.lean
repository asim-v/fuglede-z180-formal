import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B088
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D6

/-! Generated row aggregate for divisor 6, U group 88. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralRowLookupV89D6U088 : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0 => z180K30ProjectiveScalarV89D6B088Lookups
  | _ => []

theorem z180_k30_projective_literal_row_audit_v89_d6_u088
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D6.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D6.getD 88 [])
      (z180K30ProjectiveLiteralVGroupsV89D6.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 6
          (z180K30ProjectiveLiteralRowLookupV89D6U088 vIndex)) = true := by
  interval_cases vIndex
  · rw [z180K30ProjectiveLiteralUGroupV89D6G088,
      z180K30ProjectiveLiteralVGroupV89D6G000,
      ← z180K30ProjectiveScalarV89D6B088Pairs_eq]
    simpa [z180K30ProjectiveLiteralRowLookupV89D6U088] using
      z180K30ProjectiveScalarV89D6B088Audit

#print axioms z180_k30_projective_literal_row_audit_v89_d6_u088

end Fuglede.Z180K30ExceptionalRawV2
