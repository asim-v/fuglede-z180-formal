import Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B027
import Fuglede.Z180K30ExceptionalProjectiveLiteralDataV89D6

/-! Generated row aggregate for divisor 6, U group 27. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralRowLookupV89D6U027 : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  | 0 => []
  | _ => []

theorem z180_k30_projective_literal_row_audit_v89_d6_u027
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D6.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D6.getD 27 [])
      (z180K30ProjectiveLiteralVGroupsV89D6.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 6
          (z180K30ProjectiveLiteralRowLookupV89D6U027 vIndex)) = true := by
  interval_cases vIndex
  · rw [z180K30ProjectiveLiteralUGroupV89D6G027,
      z180K30ProjectiveLiteralVGroupV89D6G000,
      ← z180K30ProjectiveScalarV89D6B027Pairs_eq]
    apply normalizedProjectiveLiteralAudit_of_refutations_v89
    exact z180K30ProjectiveScalarV89D6B027Audit

#print axioms z180_k30_projective_literal_row_audit_v89_d6_u027

end Fuglede.Z180K30ExceptionalRawV2
