import Fuglede.Z180K30ExceptionalLiteralOrbitEvalV3

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_orbit_pilot_v4 :
    auditLiteralPairs z180K30ExceptionalLiteralOrbitEvalPairs =
      { enumerated := 8, accepted := 5, uncovered := 0 } := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
