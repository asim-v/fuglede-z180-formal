import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessPilotDataV87 :
    LiteralCoveredPairWitnessV87 :=
  { U := [0, 12, 24, 6, 18, 30]
    V := [0, 3, 6, 12, 18, 24]
    uRepresentative := 7
    uUnit := 1
    uTranslation := 0
    vRepresentative := 3
    vUnit := 1
    vTranslation := 12 }

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witness_pilot_v87 :
    literalCoveredPairWitnessB_v87
      z180K30ExceptionalLiteralWitnessPilotDataV87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
