import Fuglede.Z180K30ExceptionalLiteralCoreV3

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralOrbitEvalPairs : List (RawSet × RawSet) :=
  [ ([0, 1, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 10, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 10, 12, 22, 24, 34], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 15, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 15, 18, 30, 33], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 16, 18, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 21, 24, 30], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 30], [0, 6, 12, 18, 24, 30]) ]

#eval auditLiteralPairs z180K30ExceptionalLiteralOrbitEvalPairs

end Fuglede.Z180K30ExceptionalRawV2
