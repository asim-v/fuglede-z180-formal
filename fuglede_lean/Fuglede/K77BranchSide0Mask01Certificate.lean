import Fuglede.K77BranchSide0Mask01CompactCore2Linarith
import Fuglede.K77BranchSide0Mask01CompactShardedAdapter

namespace Fuglede

theorem branchUnsatAt_77_side0_mask01_from_k77BranchSide0Mask01CompactShardedCore : BranchUnsatAt 77 0 (axisSupportOfMask 1) :=
  branchUnsatAt_77_of_k77BranchSide0Mask01CompactShardedRawCertificate (by
    intro a z
    exact fuglede_k77_branch_side0_mask01_compact a z)

#print axioms branchUnsatAt_77_side0_mask01_from_k77BranchSide0Mask01CompactShardedCore

end Fuglede
