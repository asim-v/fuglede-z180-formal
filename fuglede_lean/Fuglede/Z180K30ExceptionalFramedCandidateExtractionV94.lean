import Fuglede.Z180K30ExceptionalCommonFrameTraceV93
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91

/-!
# Framed candidate extraction after the V91 orbit classifier (V94)

This module contains the constructive row-orbit part of candidate extraction.
The final candidate-list representative and coordinate transport are factored
as a small downstream interface so the V93 coefficient-covariance pilot can
be repaired independently.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

structure Z180K30CompatibleAffineRowV94 (o : Fin 7) (W : RawSet) where
  unit : RawPoint
  translation : RawPoint
  unit_mem : unit ∈ units36
  representative_to_row :
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4
          (z180K30CompatibleRowOrbitV78Fix2 o))) W = true

theorem z180K30CompatibleAffineRow_of_traceV94
    (o : Fin 7) (W : RawSet)
    (hvalidW : validSixSetB W = true)
    (hcoveredW : orbitCoveredB W = true)
    (htraceW :
      gramTraceSquare W
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936) :
    Nonempty (Z180K30CompatibleAffineRowV94 o W) := by
  rcases orbitCoveredB_forward_witness_v85Fix3 hcoveredW with
    ⟨r, rowUnit, rowTranslation, hrowUnit, hrowEq⟩
  have hvalidRep :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 r) = true := by
    fin_cases r <;> decide
  have hvalidAffine :
      validSixSetB
        (affineSet rowUnit rowTranslation
          (z180K30ExceptionalOrbitColumnV4 r)) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      rowUnit rowTranslation _ hrowUnit hvalidRep
  have hperm :
      (affineSet rowUnit rowTranslation
        (z180K30ExceptionalOrbitColumnV4 r)).Perm W :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidW hrowEq
  have htraceAffine :
      gramTraceSquare
          (affineSet rowUnit rowTranslation
            (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936 := by
    calc
      gramTraceSquare
          (affineSet rowUnit rowTranslation
            (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        gramTraceSquare W
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) :=
          gramTraceSquare_eq_of_perm_left_v88 hperm _
      _ = scalarCoeff 936 := htraceW
  have hr : r = z180K30CompatibleRowOrbitV78Fix2 o :=
    z180K30AffineTraceRowClassifierV91
      o r rowUnit rowTranslation hrowUnit htraceAffine
  subst r
  exact ⟨
    { unit := rowUnit
      translation := rowTranslation
      unit_mem := hrowUnit
      representative_to_row := hrowEq }⟩

def Z180K30CompatibleRowCandidateSelectorV94 : Prop :=
  ∀ o : Fin 7, ∀ W : RawSet,
    validSixSetB W = true →
    Nonempty (Z180K30CompatibleAffineRowV94 o W) →
    ∃ candidate ∈
      z180K30ExceptionalOrbitChoicesV4
        (z180K30NonHOrbitV78Fix2 o),
      z180K30StarSignatureV78
          (z180K30NonHOrbitV78Fix2 o) W =
        z180K30StarSignatureV78
          (z180K30NonHOrbitV78Fix2 o) candidate

#print axioms z180K30CompatibleAffineRow_of_traceV94

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

def Z180K30CommonFrameCoordinateTransportV94 : Prop :=
  ∀ U : Fin 5 → RawSet, ∀ V : RawSet,
    ∀ frame : Z180K30OrbitFrameV84Fix2 V,
      fiveGramStarB U V = true →
      Z180K30ExceptionalOrbitStarCoordinatesV4 frame.o
        (fun i => affineSet frame.unit 0 (U i))

def z180_k30_framedCandidateExtraction_of_v91_v94
    (hselector : Z180K30CompatibleRowCandidateSelectorV94)
    (hcoordinates : Z180K30CommonFrameCoordinateTransportV94) :
    Z180K30FramedCandidateExtractionV84Fix2 := by
  intro U V frame hstar hcovered ho
  let o7 : Fin 7 := ⟨frame.o.val, by
    have := frame.o.isLt
    omega⟩
  have hoEq : frame.o = z180K30NonHOrbitV78Fix2 o7 := by
    apply Fin.ext
    rfl
  let W : Fin 5 → RawSet := fun i => affineSet frame.unit 0 (U i)
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  have hvalidRep :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 frame.o) = true := by
    fin_cases frame.o <;> decide
  have hvalidW (i : Fin 5) : validSixSetB (W i) = true :=
    z180K30CommonFrameValidV93 (U i) frame.unit frame.unit_mem
      (fiveGramStar_components_v82 U V hstar i).1
  have hcoveredW (i : Fin 5) : orbitCoveredB (W i) = true :=
    z180K30CommonFrameOrbitCoveredV93
      (U i) frame.unit frame.unit_mem (hcovered i)
  have htraceW (i : Fin 5) :
      gramTraceSquare (W i)
          (z180K30ExceptionalOrbitColumnV4 frame.o) =
        scalarCoeff 936 :=
    z180K30CommonFrameTraceV93
      (U i) V (z180K30ExceptionalOrbitColumnV4 frame.o)
      frame.unit frame.translation frame.unit_mem hvalidV hvalidRep
      frame.representative_to_V
      (fiveGramStar_components_v82 U V hstar i).2.2.2
  have hrow (i : Fin 5) :
      Nonempty (Z180K30CompatibleAffineRowV94 o7 (W i)) := by
    apply z180K30CompatibleAffineRow_of_traceV94
      o7 (W i) (hvalidW i) (hcoveredW i)
    simpa only [← hoEq] using htraceW i
  choose candidate hcandidateMem hsignature using
    fun i => hselector o7 (W i) (hvalidW i) (hrow i)
  refine ⟨candidate, ?_, ?_⟩
  · intro i
    simpa only [hoEq] using hcandidateMem i
  · -- Candidate signatures are definitionally the exact V4 coordinates.
    -- The repaired V93 covariance supplies the coordinates of W; rewriting
    -- five component signatures transfers them to `candidate`.
    have hWCoordinates := hcoordinates U V frame hstar
    subst frame.o
    fin_cases o7 <;>
      simp only [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30StarSignatureV78, z180K30FiveGramCoefficientSumV4] at
          hWCoordinates ⊢ <;>
      simp_all

#print axioms z180_k30_framedCandidateExtraction_of_v91_v94

end Fuglede
