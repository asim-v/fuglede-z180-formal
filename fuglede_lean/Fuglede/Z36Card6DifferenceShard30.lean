import Fuglede.Z36Card6DifferenceCore

/-! Kernel-reduced difference-order shard with translated second point 30. -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_card6_difference_shard_30 :
    ∀ S : z36Card6RemainderCandidates (30 : ZMod 36),
      Z36Card6NineDifferencePatterns
        (insert 0 (insert (30 : ZMod 36) S.1)) := by
  decide

#print axioms z36_card6_difference_shard_30

end Fuglede
