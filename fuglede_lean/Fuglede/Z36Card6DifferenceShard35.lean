import Fuglede.Z36Card6DifferenceCore

/-! Kernel-reduced difference-order shard with translated second point 35. -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_card6_difference_shard_35 :
    ∀ S : z36Card6RemainderCandidates (35 : ZMod 36),
      Z36Card6NineDifferencePatterns
        (insert 0 (insert (35 : ZMod 36) S.1)) := by
  decide

#print axioms z36_card6_difference_shard_35

end Fuglede
