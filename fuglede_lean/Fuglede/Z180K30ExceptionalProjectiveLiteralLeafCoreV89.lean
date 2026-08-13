import Fuglede.Z180K30ExceptionalProjectiveScalarZeroV89

/-!
# Lightweight literal-leaf core for the normalized K30 projective audit

Negative leaves import only this module.  They therefore evaluate coefficient
zero without loading the V87 witness catalogue or the global normalized
enumeration.  The full literal-audit interface adds witness lookup semantics.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def normalizedProjectiveLiteralCartesianPairsV89
    (uGroup vGroup : List RawSet) : List (RawSet × RawSet) :=
  vGroup.flatMap fun V => uGroup.map fun U => (U, V)

def normalizedProjectiveScalarBothRefutedB_v89
    (pair : RawSet × RawSet) : Bool :=
  !(gramTraceScalarZeroV89 pair.1 pair.2 == 936) &&
    !(gramTraceScalarZeroV89 pair.2 pair.1 == 936)

end Fuglede.Z180K30ExceptionalRawV2
