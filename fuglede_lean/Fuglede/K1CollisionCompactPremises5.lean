import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 5. -/

namespace Fuglede

/-- Core premise 50; source assertion 924. -/
theorem k1CollisionCompactShardedCorePremise50
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 21)) > 0) → (z 1 (axisSupportOfMask 21))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 21) (by decide) hpositive

/-- Core premise 51; source assertion 926. -/
theorem k1CollisionCompactShardedCorePremise51
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 22)) > 0) → (z 1 (axisSupportOfMask 22))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 22) (by decide) hpositive

/-- Core premise 52; source assertion 928. -/
theorem k1CollisionCompactShardedCorePremise52
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 23)) > 0) → (z 1 (axisSupportOfMask 23))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 23) (by decide) hpositive

/-- Core premise 53; source assertion 930. -/
theorem k1CollisionCompactShardedCorePremise53
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 24)) > 0) → (z 1 (axisSupportOfMask 24))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 24) (by decide) hpositive

/-- Core premise 54; source assertion 932. -/
theorem k1CollisionCompactShardedCorePremise54
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 25)) > 0) → (z 1 (axisSupportOfMask 25))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 25) (by decide) hpositive

/-- Core premise 55; source assertion 934. -/
theorem k1CollisionCompactShardedCorePremise55
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 26)) > 0) → (z 1 (axisSupportOfMask 26))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 26) (by decide) hpositive

/-- Core premise 56; source assertion 936. -/
theorem k1CollisionCompactShardedCorePremise56
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 27)) > 0) → (z 1 (axisSupportOfMask 27))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 27) (by decide) hpositive

/-- Core premise 57; source assertion 938. -/
theorem k1CollisionCompactShardedCorePremise57
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 28)) > 0) → (z 1 (axisSupportOfMask 28))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 28) (by decide) hpositive

/-- Core premise 58; source assertion 940. -/
theorem k1CollisionCompactShardedCorePremise58
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 29)) > 0) → (z 1 (axisSupportOfMask 29))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 29) (by decide) hpositive

/-- Core premise 59; source assertion 942. -/
theorem k1CollisionCompactShardedCorePremise59
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 30)) > 0) → (z 1 (axisSupportOfMask 30))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 30) (by decide) hpositive

end Fuglede
