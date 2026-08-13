import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O0
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O1
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O2
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O3
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O4
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O5
import Fuglede.Z180K30ExceptionalUnitTraceRowClassifierV91O6
import Fuglede.Z180K30ExceptionalAffineCovarianceV90

/-!
# Coupled orbit-row classifier for a normalized non-H K30 column (V91)

The 49 leaves reject precisely the incompatible `(o,r)` pairs using twelve
unit images each.  This module first aggregates those leaves, then removes an
arbitrary row translation by the structural V88/V90 covariance lemmas.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180K30UnitTraceRowClassifierV91
    (o : Fin 7) (r : Fin 8) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 o := by
  fin_cases o
  · exact z180_k30_unit_trace_row_classifier_v91_o0
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o1
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o2
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o3
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o4
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o5
      r unit hunit htrace
  · exact z180_k30_unit_trace_row_classifier_v91_o6
      r unit hunit htrace

theorem affineSet_unit_translation_eq_translateV91
    (unit translation : RawPoint) (set : RawSet) :
    affineSet unit translation set =
      affineSet 1 translation (affineSet unit 0 set) := by
  symm
  simpa only [affineSet_comp_v90, one_mul,
    affinePoint_eq_mul_add_v90, one_mul, zero_add]

theorem z180K30AffineTraceRowClassifierV91
    (o : Fin 7) (r : Fin 8) (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit translation
            (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 o := by
  apply z180K30UnitTraceRowClassifierV91 o r unit hunit
  calc
    gramTraceSquare
        (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
        (z180K30ExceptionalOrbitColumnV4
          (z180K30NonHOrbitV78Fix2 o)) =
      gramTraceSquare
        (affineSet 1 translation
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r)))
        (z180K30ExceptionalOrbitColumnV4
          (z180K30NonHOrbitV78Fix2 o)) := by
        symm
        exact gramTraceSquare_translate_left_v88 _ _ translation
    _ = gramTraceSquare
          (affineSet unit translation
            (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 o)) := by
        rw [← affineSet_unit_translation_eq_translateV91]
    _ = scalarCoeff 936 := htrace

#print axioms z180K30UnitTraceRowClassifierV91
#print axioms z180K30AffineTraceRowClassifierV91

end Fuglede.Z180K30ExceptionalRawV2
