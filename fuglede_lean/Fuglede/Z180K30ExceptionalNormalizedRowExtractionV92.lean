import Fuglede.Z180K30ExceptionalCommonFrameTraceV92Fix

/-!
# Orbit witnesses and V91 classification for normalized K30 rows (V92)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

structure Z180K30NormalizedRowWitnessV92 (o : Fin 7) where
  r : Fin 8
  unit : RawPoint
  translation : RawPoint
  unit_mem : unit ∈ units36
  row_eq :
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 r))
      (z180K30ExceptionalOrbitColumnV4
        (z180K30CompatibleRowOrbitV78Fix2 o)) = true

theorem z180K30NormalizedRowOrbitWitnessV92
    (o : Fin 7) (W : RawSet)
    (hvalidW : validSixSetB W = true)
    (hcoveredW : orbitCoveredB W = true)
    (htraceW :
      gramTraceSquare W
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936) :
    ∃ witness : Z180K30NormalizedRowWitnessV92 o,
      rawSetEqB
        (affineSet witness.unit witness.translation
          (z180K30ExceptionalOrbitColumnV4 witness.r)) W = true := by
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
  let witness : Z180K30NormalizedRowWitnessV92 o :=
    { r := z180K30CompatibleRowOrbitV78Fix2 o
      unit := rowUnit
      translation := rowTranslation
      unit_mem := hrowUnit
      row_eq := hrowEq }
  exact ⟨witness, hrowEq⟩

#print axioms z180K30NormalizedRowOrbitWitnessV92

end Fuglede.Z180K30ExceptionalRawV2
