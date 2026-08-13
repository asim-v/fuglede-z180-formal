import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R0
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R1
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R2
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R3
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R4
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R5
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O3R6

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_unit_trace_row_classifier_v91_o3
    (r : Fin 8) (unit : RawPoint) (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 (3 : Fin 7))) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 (3 : Fin 7) := by
  fin_cases r
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (0 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r0
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (1 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r1
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (2 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r2
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (3 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r3
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (4 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r4
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (5 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r5
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (3 : Fin 7) (6 : Fin 8)
        z180_k30_unit_trace_reject_v91_o3_r6
        unit hunit htrace).elim
  · rfl

#print axioms z180_k30_unit_trace_row_classifier_v91_o3

end Fuglede.Z180K30ExceptionalRawV2
