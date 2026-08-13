import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 4. -/

namespace Fuglede

/-- Core premise 40; source assertion 902. -/
theorem k1CollisionCompactShardedCorePremise40
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 10)) > 0) → (z 1 (axisSupportOfMask 10))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 10) (by decide) hpositive

/-- Core premise 41; source assertion 904. -/
theorem k1CollisionCompactShardedCorePremise41
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 11)) > 0) → (z 1 (axisSupportOfMask 11))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 11) (by decide) hpositive

/-- Core premise 42; source assertion 906. -/
theorem k1CollisionCompactShardedCorePremise42
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 12)) > 0) → (z 1 (axisSupportOfMask 12))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 12) (by decide) hpositive

/-- Core premise 43; source assertion 908. -/
theorem k1CollisionCompactShardedCorePremise43
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 13)) > 0) → (z 1 (axisSupportOfMask 13))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 13) (by decide) hpositive

/-- Core premise 44; source assertion 910. -/
theorem k1CollisionCompactShardedCorePremise44
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 14)) > 0) → (z 1 (axisSupportOfMask 14))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 14) (by decide) hpositive

/-- Core premise 45; source assertion 912. -/
theorem k1CollisionCompactShardedCorePremise45
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 15)) > 0) → (z 1 (axisSupportOfMask 15))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 15) (by decide) hpositive

/-- Core premise 46; source assertion 916. -/
theorem k1CollisionCompactShardedCorePremise46
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 17)) > 0) → (z 1 (axisSupportOfMask 17))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 17) (by decide) hpositive

/-- Core premise 47; source assertion 918. -/
theorem k1CollisionCompactShardedCorePremise47
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 18)) > 0) → (z 1 (axisSupportOfMask 18))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 18) (by decide) hpositive

/-- Core premise 48; source assertion 920. -/
theorem k1CollisionCompactShardedCorePremise48
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 19)) > 0) → (z 1 (axisSupportOfMask 19))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 19) (by decide) hpositive

/-- Core premise 49; source assertion 922. -/
theorem k1CollisionCompactShardedCorePremise49
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 20)) > 0) → (z 1 (axisSupportOfMask 20))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 20) (by decide) hpositive

end Fuglede
