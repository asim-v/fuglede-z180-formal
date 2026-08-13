import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=77 branch core shard 0. -/

namespace Fuglede

/-- Core premise 0; source assertion 222. -/
theorem k77BranchSide0Mask01CompactShardedCorePremise0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 77 a z)
    : ((a 0 (axisSupportOfMask 1)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 0 (by decide)
  have hsupport : axisSupportOfMask 1 =
      ({0} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 1; source assertion 586. -/
theorem k77BranchSide0Mask01CompactShardedCorePremise1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 77 a z)
    (hbranch : HasDifferenceSupport a 0 (axisSupportOfMask 1))
    : ((a 0 (axisSupportOfMask 1)) > 0) := by
  unfold HasDifferenceSupport at hbranch
  exact hbranch

end Fuglede
