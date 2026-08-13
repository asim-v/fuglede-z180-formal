import Fuglede.Z180K30ExceptionalUnitTraceClassifierCoreV91

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180_k30_unit_trace_reject_v91_o2_r1 :
    z180K30UnitTraceRejectAuditV91 (2 : Fin 7) (1 : Fin 8) = true := by
  decide

#print axioms z180_k30_unit_trace_reject_v91_o2_r1

end Fuglede.Z180K30ExceptionalRawV2
