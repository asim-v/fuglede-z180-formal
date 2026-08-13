import Fuglede.Z180K30ExceptionalCommonFrameCovarianceV93
import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalAffineCandidateAuditAggregateV95

/-!
# Same-frame candidate extraction for the exceptional K30 star (V95)

The column frame is used with the same unit on every row.  V91 selects the
unique compatible row orbit, the small fixed-unit affine table selects an
equal V4 candidate, and V93 transports the five star coordinates into that
common frame.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

/-- Reordering the row set leaves every entry of its Gram list unchanged. -/
theorem gram_eq_of_perm_left_v95
    {left right : RawSet} (hperm : left.Perm right) (V : RawSet) :
    gram left V = gram right V := by
  unfold gram
  apply List.flatMap_congr
  intro row hrow
  apply List.map_congr_left
  intro column hcolumn
  apply coeffSum_eq_of_perm_v88
  exact hperm.map fun point =>
    zetaPower
      (point.val * ((column.val + 36 - row.val) % 36))

/-- Consequently the V78 signature is invariant under row reordering. -/
theorem z180K30StarSignature_eq_of_perm_left_v95
    (o : Fin 8) {left right : RawSet} (hperm : left.Perm right) :
    z180K30StarSignatureV78 o left =
      z180K30StarSignatureV78 o right := by
  fin_cases o <;>
    simp only [z180K30StarSignatureV78] <;>
    simp_rw [gram_eq_of_perm_left_v95 hperm]

/-- Equality of the five row signatures transports the exact V4 star
coordinates.  Factoring this finite case split out of the dependent frame
construction keeps the orbit index nondependent. -/
theorem z180K30StarCoordinates_of_signatures_v95
    (o : Fin 7) (left right : Fin 5 → RawSet)
    (hsignature : ∀ i,
      z180K30StarSignatureV78 (z180K30NonHOrbitV78Fix2 o) (left i) =
        z180K30StarSignatureV78 (z180K30NonHOrbitV78Fix2 o) (right i))
    (hleft : Z180K30ExceptionalOrbitStarCoordinatesV4
      (z180K30NonHOrbitV78Fix2 o) left) :
    Z180K30ExceptionalOrbitStarCoordinatesV4
      (z180K30NonHOrbitV78Fix2 o) right := by
  fin_cases o <;>
    simp only [Z180K30ExceptionalOrbitStarCoordinatesV4,
      z180K30NonHOrbitV78Fix2, z180K30StarSignatureV78,
      z180K30FiveGramCoefficientSumV4] at hleft hsignature ⊢ <;>
    simp_all

/-- A valid covered row of trace 936 against a normalized non-H column has a
candidate in that column's V4 choice list with the same exact signature. -/
theorem z180K30CompatibleSignatureCandidate_of_trace_v95
    (o : Fin 7) (W : RawSet)
    (hvalidW : validSixSetB W = true)
    (hcoveredW : orbitCoveredB W = true)
    (htraceW :
      gramTraceSquare W
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936) :
    ∃ candidate ∈
        z180K30ExceptionalOrbitChoicesV4
          (z180K30NonHOrbitV78Fix2 o),
      z180K30StarSignatureV78
          (z180K30NonHOrbitV78Fix2 o) W =
        z180K30StarSignatureV78
          (z180K30NonHOrbitV78Fix2 o) candidate := by
  rcases orbitCoveredB_forward_witness_v85Fix3 hcoveredW with
    ⟨r, rowUnit, rowTranslation, hrowUnit, hrowEq⟩
  let affineRow :=
    affineSet rowUnit rowTranslation
      (z180K30ExceptionalOrbitColumnV4 r)
  have hvalidRepresentative :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 r) = true := by
    fin_cases r <;> decide
  have hvalidAffineRow : validSixSetB affineRow = true := by
    exact validSixSetB_affine_of_unit_v85Fix3
      rowUnit rowTranslation _ hrowUnit hvalidRepresentative
  have hperm : affineRow.Perm W := by
    exact perm_of_rawSetEqB_of_valid_v88
      hvalidAffineRow hvalidW hrowEq
  have htraceAffineRow :
      gramTraceSquare affineRow
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936 := by
    calc
      gramTraceSquare affineRow
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        gramTraceSquare W
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) :=
          gramTraceSquare_eq_of_perm_left_v88 hperm _
      _ = scalarCoeff 936 := htraceW
  have hr : r = z180K30CompatibleRowOrbitV78Fix2 o := by
    exact z180K30AffineTraceRowClassifierV91
      o r rowUnit rowTranslation hrowUnit htraceAffineRow
  subst r
  rcases z180K30CompatibleAffineCandidate_of_unit_v95
      o rowUnit rowTranslation hrowUnit with
    ⟨candidate, hcandidate, hvalidCandidate, hcandidateEq⟩
  have hpermCandidate : affineRow.Perm candidate := by
    apply perm_of_rawSetEqB_of_valid_v88
      hvalidAffineRow hvalidCandidate
    simpa only [affineRow] using hcandidateEq
  have hpermWCandidate : W.Perm candidate :=
    hperm.symm.trans hpermCandidate
  refine ⟨candidate, hcandidate, ?_⟩
  exact z180K30StarSignature_eq_of_perm_left_v95
    (z180K30NonHOrbitV78Fix2 o) hpermWCandidate

#print axioms gram_eq_of_perm_left_v95
#print axioms z180K30CompatibleSignatureCandidate_of_trace_v95

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

/-- Complete candidate extraction in the same-unit V93 frame. -/
def z180_k30_framedCandidateExtraction_v95 :
    Z180K30FramedCandidateExtractionV84Fix2 := by
  intro U V frame hstar hcovered ho
  have hoVal : frame.o.val ≠ 7 := by
    intro hval
    apply ho
    apply Fin.ext
    exact hval
  let o7 : Fin 7 := ⟨frame.o.val, by
    have := frame.o.isLt
    omega⟩
  have hoEq : frame.o = z180K30NonHOrbitV78Fix2 o7 := by
    apply Fin.ext
    rfl
  let W : Fin 5 → RawSet := fun i => affineSet frame.unit 0 (U i)
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  have hvalidRepresentative :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 frame.o) = true := by
    have hall : ∀ o : Fin 8,
        validSixSetB (z180K30ExceptionalOrbitColumnV4 o) = true := by
      intro o
      fin_cases o <;> decide
    exact hall frame.o
  have hvalidW (i : Fin 5) : validSixSetB (W i) = true :=
    z180K30CommonFrameValidV93
      (U i) frame.unit frame.unit_mem
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
      frame.unit frame.translation frame.unit_mem
      hvalidV hvalidRepresentative frame.representative_to_V
      (fiveGramStar_components_v82 U V hstar i).2.2.2
  have hcandidate (i : Fin 5) :
      ∃ candidate ∈
          z180K30ExceptionalOrbitChoicesV4
            (z180K30NonHOrbitV78Fix2 o7),
        z180K30StarSignatureV78
            (z180K30NonHOrbitV78Fix2 o7) (W i) =
          z180K30StarSignatureV78
            (z180K30NonHOrbitV78Fix2 o7) candidate := by
    apply z180K30CompatibleSignatureCandidate_of_trace_v95
      o7 (W i) (hvalidW i) (hcoveredW i)
    simpa only [← hoEq] using htraceW i
  choose candidate hcandidateMem hsignature using hcandidate
  refine ⟨candidate, ?_, ?_⟩
  · intro i
    simpa only [hoEq] using hcandidateMem i
  · have hWCoordinates := fiveGramStar_commonFrameCoordinates_v93
      U V frame.o frame.unit frame.translation frame.unit_mem
      frame.representative_to_V hstar
    rw [hoEq] at hWCoordinates
    exact z180K30StarCoordinates_of_signatures_v95
      o7 W candidate hsignature hWCoordinates

/-- The V85 frame extractor and V95 candidate extractor instantiate the
framed catalogue interface with no remaining hypothesis. -/
noncomputable def z180_k30_exceptionalFramedStarCatalogue_v95 :
    Z180K30ExceptionalFramedStarCatalogueV83 :=
  z180_k30_framedStarCatalogue_of_interfaces_v84Fix2
    z180_k30_orbitFrameExtraction_v85Fix3
    z180_k30_framedCandidateExtraction_v95

#print axioms z180_k30_framedCandidateExtraction_v95
#print axioms z180_k30_exceptionalFramedStarCatalogue_v95

end Fuglede
