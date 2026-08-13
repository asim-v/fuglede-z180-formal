import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B062
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D6

/-! Generated row aggregate for divisor 6, U group 62. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralRowLookupV89D6U062 : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0 => z180K30ProjectiveScalarV89D6B062Lookups
  | _ => []

theorem z180_k30_projective_literal_row_audit_v89_d6_u062
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D6.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D6.getD 62 [])
      (z180K30ProjectiveLiteralVGroupsV89D6.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 6
          (z180K30ProjectiveLiteralRowLookupV89D6U062 vIndex)) = true := by
  interval_cases vIndex
  · rw [z180K30ProjectiveLiteralUGroupV89D6G062,
      z180K30ProjectiveLiteralVGroupV89D6G000,
      ← z180K30ProjectiveScalarV89D6B062Pairs_eq]
    simpa [z180K30ProjectiveLiteralRowLookupV89D6U062] using
      z180K30ProjectiveScalarV89D6B062Audit

#print axioms z180_k30_projective_literal_row_audit_v89_d6_u062

end Fuglede.Z180K30ExceptionalRawV2
