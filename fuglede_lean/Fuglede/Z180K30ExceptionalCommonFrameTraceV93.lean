import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalAffineCovarianceV90
import Fuglede.Z180K30FiveGramStarSemanticsV82

/-!
# Same-unit transport into a common exceptional column frame (V93)

If the actual column is the affine image `a • R + b`, its Fourier difference
is multiplied by `a`.  Consequently the correctly normalized row is
`a • U`, with the same unit (not its inverse).  These lemmas isolate that
orientation and expose exactly the trace, validity, and orbit-coverage facts
needed by the framed candidate selector.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180K30CommonFrameTraceV93
    (U V representative : RawSet)
    (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hvalidV : validSixSetB V = true)
    (hvalidRepresentative : validSixSetB representative = true)
    (hframe :
      rawSetEqB (affineSet unit translation representative) V = true)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    gramTraceSquare (affineSet unit 0 U) representative =
      scalarCoeff 936 := by
  have hvalidAffine :
      validSixSetB (affineSet unit translation representative) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      unit translation representative hunit hvalidRepresentative
  have hperm :
      (affineSet unit translation representative).Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  calc
    gramTraceSquare (affineSet unit 0 U) representative =
        gramTraceSquare U (affineSet unit translation representative) :=
      gramTraceSquare_affine_covariant_v90
        U representative unit 0 translation
    _ = gramTraceSquare U V :=
      gramTraceSquare_eq_of_perm_right_v88 U hperm
    _ = scalarCoeff 936 := htrace

theorem z180K30CommonFrameValidV93
    (U : RawSet) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (hvalid : validSixSetB U = true) :
    validSixSetB (affineSet unit 0 U) = true :=
  validSixSetB_affine_of_unit_v85Fix3 unit 0 U hunit hvalid

theorem z180K30CommonFrameOrbitCoveredV93
    (U : RawSet) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (hcovered : orbitCoveredB U = true) :
    orbitCoveredB (affineSet unit 0 U) = true :=
  orbitCoveredB_affine_forward_v90 U unit 0 hunit hcovered

#print axioms z180K30CommonFrameTraceV93
#print axioms z180K30CommonFrameValidV93
#print axioms z180K30CommonFrameOrbitCoveredV93

end Fuglede.Z180K30ExceptionalRawV2
