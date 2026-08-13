import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R0
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R1
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R3
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R4
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R5
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R6
import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O4R7

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_unit_trace_row_classifier_v91_o4
    (r : Fin 8) (unit : RawPoint) (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 (4 : Fin 7))) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 (4 : Fin 7) := by
  fin_cases r
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (0 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r0
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (1 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r1
        unit hunit htrace).elim
  · rfl
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (3 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r3
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (4 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r4
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (5 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r5
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (6 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r6
        unit hunit htrace).elim
  · exact
      (z180K30UnitTraceRejectAudit_semanticsV91
        (4 : Fin 7) (7 : Fin 8)
        z180_k30_unit_trace_reject_v91_o4_r7
        unit hunit htrace).elim

#print axioms z180_k30_unit_trace_row_classifier_v91_o4

end Fuglede.Z180K30ExceptionalRawV2
