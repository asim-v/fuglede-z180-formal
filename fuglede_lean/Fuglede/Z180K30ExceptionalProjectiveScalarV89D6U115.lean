import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B115
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D6

/-! Generated row aggregate for divisor 6, U group 115. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralRowLookupV89D6U115 : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0 => []
  | _ => []

theorem z180_k30_projective_literal_row_audit_v89_d6_u115
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D6.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D6.getD 115 [])
      (z180K30ProjectiveLiteralVGroupsV89D6.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 6
          (z180K30ProjectiveLiteralRowLookupV89D6U115 vIndex)) = true := by
  interval_cases vIndex
  · rw [z180K30ProjectiveLiteralUGroupV89D6G115,
      z180K30ProjectiveLiteralVGroupV89D6G000,
      ← z180K30ProjectiveScalarV89D6B115Pairs_eq]
    apply normalizedProjectiveLiteralAudit_of_refutations_v89
    exact z180K30ProjectiveScalarV89D6B115Audit

#print axioms z180_k30_projective_literal_row_audit_v89_d6_u115

end Fuglede.Z180K30ExceptionalRawV2
