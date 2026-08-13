import Fuglede.Z180K30ExceptionalCatalogueKernelsV83
import Fuglede.Z180K30ExceptionalOrbitSignatureWitnessV78Fix2

/-!
# Explicit common-frame interfaces for the K30 catalogue (V84)

This module isolates the two structural facts still needed to turn marginal
orbit coverage into the V65 catalogue witness.  Neither fact is hidden behind
an opaque `Prop`: both expose the common affine frame and the five candidate
sets used by the star obstruction.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

/-- A concrete orientation of one `orbitCoveredB V` witness.  The orientation
matches the `affineOrbit` field required by V65. -/
structure Z180K30OrbitFrameV84 (V : RawSet) where
  o : Fin 8
  unit : RawPoint
  translation : RawPoint
  unit_mem : unit ∈ units36
  representative_to_V :
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 o)) V = true
  V_to_representative :
    affineEquivalentB V
      (z180K30ExceptionalOrbitColumnV4 o) = true

/-- Semantic extraction of a concrete frame from Boolean orbit coverage.
The reverse orientation requires the explicit inverse unit modulo 36. -/
def Z180K30OrbitFrameExtractionV84 : Prop :=
  ∀ V : RawSet, validSixSetB V = true → orbitCoveredB V = true →
    Nonempty (Z180K30OrbitFrameV84 V)

/-- In one common column frame, all five covered exceptional rows can be
replaced by literal candidates without changing the exact star coordinates.
This is the coupled finite statement: the frame is shared, rather than chosen
independently for each pair. -/
def Z180K30FramedCandidateExtractionV84 : Prop :=
  ∀ U : Fin 5 → RawSet, ∀ V : RawSet,
    ∀ frame : Z180K30OrbitFrameV84 V,
      fiveGramStarB U V = true →
      (∀ i, orbitCoveredB (U i) = true) →
      frame.o ≠ 7 →
      ∃ U' : Fin 5 → RawSet,
        (∀ i, U' i ∈
          z180K30ExceptionalOrbitChoicesV4 frame.o) ∧
        Z180K30ExceptionalOrbitStarCoordinatesV4 frame.o U'

/-- The framed catalogue kernel follows directly from the two explicit
interfaces above. -/
theorem z180_k30_framedStarCatalogue_of_interfaces_v84
    (hframe : Z180K30OrbitFrameExtractionV84)
    (hcandidates : Z180K30FramedCandidateExtractionV84) :
    Z180K30ExceptionalFramedStarCatalogueV83 := by
  intro U V hstar hU hV
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  rcases hframe V hvalidV hV with ⟨frame⟩
  refine
    { validSixSet := hvalidV
      o := frame.o
      affineOrbit := frame.V_to_representative
      starAlternative := ?_ }
  by_cases ho : frame.o = 7
  · exact Or.inl ho
  · exact Or.inr (hcandidates U V frame hstar hU ho)

/-- Stable endpoint for the terminal K30 assembly. -/
theorem z180_k30_fiveGramStar_catalogue_of_orbitCovered_v84
    (hframe : Z180K30OrbitFrameExtractionV84)
    (hcandidates : Z180K30FramedCandidateExtractionV84)
    {U : Fin 5 → RawSet} {V : RawSet}
    (hstar : fiveGramStarB U V = true)
    (hU : ∀ i, orbitCoveredB (U i) = true)
    (hV : orbitCoveredB V = true) :
    Z180K30CatalogueAlternativeV65 V :=
  z180_k30_framedStarCatalogue_of_interfaces_v84
    hframe hcandidates U V hstar hU hV

#print axioms z180_k30_framedStarCatalogue_of_interfaces_v84
#print axioms z180_k30_fiveGramStar_catalogue_of_orbitCovered_v84

end Fuglede
