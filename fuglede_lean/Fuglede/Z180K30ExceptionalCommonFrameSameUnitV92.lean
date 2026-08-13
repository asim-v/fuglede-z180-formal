import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91
import Fuglede.Z180K30ExceptionalAffineCovarianceV90

/-!
# Same-unit common-frame transport for the K30 star (V92)

If the column frame is `V = a R_o + b`, the normalized row is `a U`, not
`a⁻¹ U`.  This is exactly the orientation of V90 covariance.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180K30CommonFrameTraceV92
    (U V : RawSet) (o : Fin 8) (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hvalidV : validSixSetB V = true)
    (hframe :
      rawSetEqB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) V = true)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    gramTraceSquare (affineSet unit 0 U)
        (z180K30ExceptionalOrbitColumnV4 o) = scalarCoeff 936 := by
  have hvalidRep :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 o) = true := by
    fin_cases o <;> decide
  have hvalidAffine :
      validSixSetB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      unit translation _ hunit hvalidRep
  have hperm :
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 o)).Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  calc
    gramTraceSquare (affineSet unit 0 U)
        (z180K30ExceptionalOrbitColumnV4 o) =
      gramTraceSquare U
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) :=
        gramTraceSquare_affine_covariant_v90 U
          (z180K30ExceptionalOrbitColumnV4 o) unit 0 translation
    _ = gramTraceSquare U V :=
      gramTraceSquare_eq_of_perm_right_v88 U hperm
    _ = scalarCoeff 936 := htrace

theorem z180K30CommonFrameOrbitCoveredV92
    (U : RawSet) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (hcovered : orbitCoveredB U = true) :
    orbitCoveredB (affineSet unit 0 U) = true :=
  orbitCoveredB_affine_forward_v90 U unit 0 hunit hcovered

theorem z180K30CommonFrameValidV92
    (U : RawSet) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (hvalid : validSixSetB U = true) :
    validSixSetB (affineSet unit 0 U) = true :=
  validSixSetB_affine_of_unit_v85Fix3 unit 0 U hunit hvalid

#print axioms z180K30CommonFrameTraceV92
#print axioms z180K30CommonFrameOrbitCoveredV92

end Fuglede.Z180K30ExceptionalRawV2
