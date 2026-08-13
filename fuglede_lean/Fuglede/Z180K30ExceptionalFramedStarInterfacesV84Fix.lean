import Fuglede.Z180K30ExceptionalCatalogueKernelsV83
import Fuglede.Z180K30ExceptionalOrbitSignatureWitnessV78Fix2

/-! # Constructive common-frame interfaces for the K30 catalogue (V84 Fix) -/

namespace Fuglede

open Z180K30ExceptionalRawV2

structure Z180K30OrbitFrameV84Fix (V : RawSet) where
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

def Z180K30OrbitFrameExtractionV84Fix : Type :=
  ∀ V : RawSet, validSixSetB V = true → orbitCoveredB V = true →
    Z180K30OrbitFrameV84Fix V

def Z180K30FramedCandidateExtractionV84Fix : Type :=
  ∀ U : Fin 5 → RawSet, ∀ V : RawSet,
    ∀ frame : Z180K30OrbitFrameV84Fix V,
      fiveGramStarB U V = true →
      (∀ i, orbitCoveredB (U i) = true) →
      frame.o ≠ 7 →
      ∃ U' : Fin 5 → RawSet,
        (∀ i, U' i ∈
          z180K30ExceptionalOrbitChoicesV4 frame.o) ∧
        Z180K30ExceptionalOrbitStarCoordinatesV4 frame.o U'

def z180_k30_framedStarCatalogue_of_interfaces_v84Fix
    (hframe : Z180K30OrbitFrameExtractionV84Fix)
    (hcandidates : Z180K30FramedCandidateExtractionV84Fix) :
    Z180K30ExceptionalFramedStarCatalogueV83 := by
  intro U V hstar hU hV
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  let frame := hframe V hvalidV hV
  refine
    { validSixSet := hvalidV
      o := frame.o
      affineOrbit := frame.V_to_representative
      starAlternative := ?_ }
  by_cases ho : frame.o = 7
  · exact Or.inl ho
  · exact Or.inr (hcandidates U V frame hstar hU ho)

def z180_k30_fiveGramStar_catalogue_of_orbitCovered_v84Fix
    (hframe : Z180K30OrbitFrameExtractionV84Fix)
    (hcandidates : Z180K30FramedCandidateExtractionV84Fix)
    {U : Fin 5 → RawSet} {V : RawSet}
    (hstar : fiveGramStarB U V = true)
    (hU : ∀ i, orbitCoveredB (U i) = true)
    (hV : orbitCoveredB V = true) :
    Z180K30CatalogueAlternativeV65 V :=
  z180_k30_framedStarCatalogue_of_interfaces_v84Fix
    hframe hcandidates U V hstar hU hV

#print axioms z180_k30_framedStarCatalogue_of_interfaces_v84Fix
#print axioms z180_k30_fiveGramStar_catalogue_of_orbitCovered_v84Fix

end Fuglede
