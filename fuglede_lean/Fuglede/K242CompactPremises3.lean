import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 3. -/

namespace Fuglede

/-- Core premise 30; source assertion 253. -/
theorem k242CorePremise30
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 5)) ≥ 0) := by
  exact hconstraints.nonnegative 1 (axisSupportOfMask 5)

/-- Core premise 31; source assertion 295. -/
theorem k242CorePremise31
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 19)) ≥ 0) := by
  exact hconstraints.nonnegative 1 (axisSupportOfMask 19)

/-- Core premise 32; source assertion 313. -/
theorem k242CorePremise32
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 25)) ≥ 0) := by
  exact hconstraints.nonnegative 1 (axisSupportOfMask 25)

/-- Core premise 33; source assertion 334. -/
theorem k242CorePremise33
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 1)) + (a 1 (axisSupportOfMask 2)) + (a 1 (axisSupportOfMask 3)) + (a 1 (axisSupportOfMask 4)) + (a 1 (axisSupportOfMask 5)) + (a 1 (axisSupportOfMask 6)) + (a 1 (axisSupportOfMask 7)) + (a 1 (axisSupportOfMask 8)) + (a 1 (axisSupportOfMask 9)) + (a 1 (axisSupportOfMask 10)) + (a 1 (axisSupportOfMask 11)) + (a 1 (axisSupportOfMask 12)) + (a 1 (axisSupportOfMask 13)) + (a 1 (axisSupportOfMask 14)) + (a 1 (axisSupportOfMask 15)) + (a 1 (axisSupportOfMask 16)) + (a 1 (axisSupportOfMask 17)) + (a 1 (axisSupportOfMask 18)) + (a 1 (axisSupportOfMask 19)) + (a 1 (axisSupportOfMask 20)) + (a 1 (axisSupportOfMask 21)) + (a 1 (axisSupportOfMask 22)) + (a 1 (axisSupportOfMask 23)) + (a 1 (axisSupportOfMask 24)) + (a 1 (axisSupportOfMask 25)) + (a 1 (axisSupportOfMask 26)) + (a 1 (axisSupportOfMask 27)) + (a 1 (axisSupportOfMask 28)) + (a 1 (axisSupportOfMask 29)) + (a 1 (axisSupportOfMask 30)) + (a 1 (axisSupportOfMask 31))) = 58564) := by
  have hmass := hconstraints.total_mass 1
  rw [sum_axisSupportOfMask_explicit] at hmass
  norm_num at hmass ⊢
  linarith only [hmass]

/-- Core premise 34; source assertion 341. -/
theorem k242CorePremise34
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 4)) + (a 1 (axisSupportOfMask 8)) + (a 1 (axisSupportOfMask 12)) + (a 1 (axisSupportOfMask 16)) + (a 1 (axisSupportOfMask 20)) + (a 1 (axisSupportOfMask 24)) + (a 1 (axisSupportOfMask 28))) ≥ 9762) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 3)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 3) = 9762 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 35; source assertion 361. -/
theorem k242CorePremise35
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 2)) + (a 1 (axisSupportOfMask 16)) + (a 1 (axisSupportOfMask 18))) ≥ 854) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 13)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 13) = 854 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 36; source assertion 373. -/
theorem k242CorePremise36
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 4)) + (a 1 (axisSupportOfMask 8)) + (a 1 (axisSupportOfMask 12))) ≥ 902) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 19)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 19) = 902 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 37; source assertion 377. -/
theorem k242CorePremise37
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 2)) + (a 1 (axisSupportOfMask 8)) + (a 1 (axisSupportOfMask 10))) ≥ 550) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 21)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 21) = 550 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 38; source assertion 379. -/
theorem k242CorePremise38
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 1)) + (a 1 (axisSupportOfMask 8)) + (a 1 (axisSupportOfMask 9))) ≥ 396) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 22)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 22) = 396 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 39; source assertion 385. -/
theorem k242CorePremise39
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 0)) + (a 1 (axisSupportOfMask 2)) + (a 1 (axisSupportOfMask 4)) + (a 1 (axisSupportOfMask 6))) ≥ 418) := by
  have hprojection := hconstraints.projection_lower 1 (axisSupportOfMask 25)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 25) = 418 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

end Fuglede
