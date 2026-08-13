import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 6. -/

namespace Fuglede

/-- Core premise 60; source assertion 497. -/
theorem k242CorePremise60
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 9)) > 0) → (z 0 (axisSupportOfMask 9))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 9) (by decide) hpositive

/-- Core premise 61; source assertion 498. -/
theorem k242CorePremise61
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 10)) > 0) → (z 1 (axisSupportOfMask 10))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 10) (by decide) hpositive

/-- Core premise 62; source assertion 499. -/
theorem k242CorePremise62
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 10)) > 0) → (z 0 (axisSupportOfMask 10))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 10) (by decide) hpositive

/-- Core premise 63; source assertion 502. -/
theorem k242CorePremise63
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 12)) > 0) → (z 1 (axisSupportOfMask 12))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 12) (by decide) hpositive

/-- Core premise 64; source assertion 503. -/
theorem k242CorePremise64
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 12)) > 0) → (z 0 (axisSupportOfMask 12))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 12) (by decide) hpositive

/-- Core premise 65; source assertion 506. -/
theorem k242CorePremise65
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 14)) > 0) → (z 1 (axisSupportOfMask 14))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 14) (by decide) hpositive

/-- Core premise 66; source assertion 508. -/
theorem k242CorePremise66
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 15)) > 0) → (z 1 (axisSupportOfMask 15))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 15) (by decide) hpositive

/-- Core premise 67; source assertion 510. -/
theorem k242CorePremise67
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 16)) > 0) → (z 1 (axisSupportOfMask 16))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 16) (by decide) hpositive

/-- Core premise 68; source assertion 515. -/
theorem k242CorePremise68
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 18)) > 0) → (z 0 (axisSupportOfMask 18))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 18) (by decide) hpositive

/-- Core premise 69; source assertion 527. -/
theorem k242CorePremise69
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 24)) > 0) → (z 0 (axisSupportOfMask 24))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 24) (by decide) hpositive

end Fuglede
