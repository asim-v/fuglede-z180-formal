import Fuglede.Z180K30ExceptionalLiteralCoreV3

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralOrbitPilotPairs : List (RawSet × RawSet) :=
  [ ([0, 1, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 10, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 10, 12, 22, 24, 34], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 15, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 15, 18, 30, 33], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 16, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 21, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]) ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_orbit_pilot_v3 :
    auditLiteralPairs z180K30ExceptionalLiteralOrbitPilotPairs =
      { enumerated := 8, accepted := 4, uncovered := 0 } := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
