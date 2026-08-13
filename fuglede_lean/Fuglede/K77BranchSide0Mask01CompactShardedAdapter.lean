import Fuglede.K77BranchSide0Mask01CompactPremises0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Minimal sharded compact branch adapter for pinned k=77.
SMT SHA-256: `9aa103c66ca1a2303e589a768d28fa13d2a789be95f0d1c56a59b1a1c615d3c7`.
Core-index SHA-256: `a95ff7bd531dda3be77b2b515af5d15bdc1fda99d3451f40aa2db5681b8ec356`.
-/

namespace Fuglede

def K77BranchSide0Mask01CompactShardedRawCertificate : Prop :=
  ∀ (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop),
    -- core premise 0; source assertion 222
    ((a 0 1) = 0) →
    -- core premise 1; source assertion 586
    ((a 0 1) > 0) →
    False

theorem branchUnsatAt_77_of_k77BranchSide0Mask01CompactShardedRawCertificate
    (hraw : K77BranchSide0Mask01CompactShardedRawCertificate) : BranchUnsatAt 77 0 (axisSupportOfMask 1) := by
  intro a z hconstraints hbranch
  unfold K77BranchSide0Mask01CompactShardedRawCertificate at hraw
  apply hraw
    (fun s m => a s (axisSupportOfMask m.val))
    (fun s m => z s (axisSupportOfMask m.val))
  · exact k77BranchSide0Mask01CompactShardedCorePremise0 a z hconstraints
  · exact k77BranchSide0Mask01CompactShardedCorePremise1 a z hconstraints hbranch

end Fuglede
