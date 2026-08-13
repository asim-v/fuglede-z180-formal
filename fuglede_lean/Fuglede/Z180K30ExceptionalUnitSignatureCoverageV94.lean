import Fuglede.Z180K30ExceptionalOrbitSignatureWitnessV78Fix2
import Mathlib.Tactic

/-!
# Exact unit-signature coverage for the seven non-H column orbits (V94)

This is the small finite table needed after the structural V91 row-orbit
classifier.  Translation and list-order transport are deliberately left to
the framed candidate adapter.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem z180K30CompatibleUnitSignatureCovered_v94
    (o : Fin 7) (unit : RawPoint) (hunit : unit ∈ units36) :
    z180K30SignatureCoveredBV78 (z180K30NonHOrbitV78Fix2 o)
      (affineSet unit 0
        (z180K30ExceptionalOrbitColumnV4
          (z180K30CompatibleRowOrbitV78Fix2 o))) = true := by
  fin_cases o <;> fin_cases unit <;>
    simp_all [units36, z180K30SignatureCoveredBV78,
      z180K30ExceptionalOrbitChoicesV4, z180K30StarSignatureV78,
      z180K30NonHOrbitV78Fix2, z180K30CompatibleRowOrbitV78Fix2,
      affineSet, affinePoint, gram, gramCoefficientV2, coeffSum,
      zetaPower, zetaPowerTable, coeffAdd, coeffZero]

#print axioms z180K30CompatibleUnitSignatureCovered_v94

end Fuglede.Z180K30ExceptionalRawV2
