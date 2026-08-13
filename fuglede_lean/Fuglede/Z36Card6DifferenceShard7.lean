import Fuglede.Z36Card6DifferenceCore

/-! Kernel-reduced difference-order shard with translated second point 7. -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_card6_difference_shard_7 :
    ∀ S : z36Card6RemainderCandidates (7 : ZMod 36),
      Z36Card6NineDifferencePatterns
        (insert 0 (insert (7 : ZMod 36) S.1)) := by
  decide

#print axioms z36_card6_difference_shard_7

end Fuglede
