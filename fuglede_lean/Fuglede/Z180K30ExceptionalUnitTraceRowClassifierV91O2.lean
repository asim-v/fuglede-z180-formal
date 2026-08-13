import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R0
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R1
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R2
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R3
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R5
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R6
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O2R7

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_unit_trace_row_classifier_v91_o2
    (r : Fin 8) (unit : RawPoint) (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 (2 : Fin 7))) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 (2 : Fin 7) := by
  fin_cases r
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (0 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r0
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (1 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r1
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (2 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r2
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (3 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r3
        unit hunit htrace).elim
  · rfl
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (5 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r5
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (6 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r6
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (2 : Fin 7) (7 : Fin 8)
        z180_k30_unit_trace_reject_v91_o2_r7
        unit hunit htrace).elim

#print axioms z180_k30_unit_trace_row_classifier_v91_o2

end Fuglede.Z180K30ExceptionalRawV2
