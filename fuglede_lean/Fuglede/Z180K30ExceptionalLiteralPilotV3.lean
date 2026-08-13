import Fuglede.Z180K30ExceptionalLiteralCoreV3

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralPilotPairs : List (RawSet × RawSet) :=
  [([0, 1, 6, 12, 18, 24], [0, 6, 12, 18, 24, 30])]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_pilot_v3 :
    auditLiteralPairs z180K30ExceptionalLiteralPilotPairs =
      { enumerated := 1, accepted := 1, uncovered := 0 } := by
  decide

end Fuglede.Z180K30ExceptionalRawV2

