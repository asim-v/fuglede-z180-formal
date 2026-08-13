import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 0. -/

namespace Fuglede

/-- Core premise 0; source assertion 0. -/
theorem k242CorePremise0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 0 (axisSupportOfMask 0)) = 242) := by
  simpa [axisSupportOfMask] using hconstraints.diagonal 0

/-- Core premise 1; source assertion 7. -/
theorem k242CorePremise1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 0 (axisSupportOfMask 3)) ≥ 0) := by
  exact hconstraints.nonnegative 0 (axisSupportOfMask 3)

/-- Core premise 2; source assertion 125. -/
theorem k242CorePremise2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 16))) ≥ 306) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 15)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 15) = 306 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 3; source assertion 131. -/
theorem k242CorePremise3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 1)) + (a 0 (axisSupportOfMask 4)) + (a 0 (axisSupportOfMask 5)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 9)) + (a 0 (axisSupportOfMask 12)) + (a 0 (axisSupportOfMask 13))) ≥ 1782) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 18)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 18) = 1782 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 4; source assertion 133. -/
theorem k242CorePremise4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 4)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 12))) ≥ 902) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 19)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 19) = 902 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 5; source assertion 137. -/
theorem k242CorePremise5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 2)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 10))) ≥ 550) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 21)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 21) = 550 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 6; source assertion 139. -/
theorem k242CorePremise6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 1)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 9))) ≥ 396) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 22)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 242 (maskSupportModulus 22) = 396 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit] at hprojection
  simp at hprojection ⊢
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 7; source assertion 163. -/
theorem k242CorePremise7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((2 * (a 0 (axisSupportOfMask 0))) + ((-2) * (a 0 (axisSupportOfMask 1))) + ((-1) * (a 0 (axisSupportOfMask 2))) + (1 * (a 0 (axisSupportOfMask 3))) + (2 * (a 0 (axisSupportOfMask 4))) + ((-2) * (a 0 (axisSupportOfMask 5))) + ((-1) * (a 0 (axisSupportOfMask 6))) + (1 * (a 0 (axisSupportOfMask 7))) + (2 * (a 0 (axisSupportOfMask 8))) + ((-2) * (a 0 (axisSupportOfMask 9))) + ((-1) * (a 0 (axisSupportOfMask 10))) + (1 * (a 0 (axisSupportOfMask 11))) + (2 * (a 0 (axisSupportOfMask 12))) + ((-2) * (a 0 (axisSupportOfMask 13))) + ((-1) * (a 0 (axisSupportOfMask 14))) + (1 * (a 0 (axisSupportOfMask 15))) + (2 * (a 0 (axisSupportOfMask 16))) + ((-2) * (a 0 (axisSupportOfMask 17))) + ((-1) * (a 0 (axisSupportOfMask 18))) + (1 * (a 0 (axisSupportOfMask 19))) + (2 * (a 0 (axisSupportOfMask 20))) + ((-2) * (a 0 (axisSupportOfMask 21))) + ((-1) * (a 0 (axisSupportOfMask 22))) + (1 * (a 0 (axisSupportOfMask 23))) + (2 * (a 0 (axisSupportOfMask 24))) + ((-2) * (a 0 (axisSupportOfMask 25))) + ((-1) * (a 0 (axisSupportOfMask 26))) + (1 * (a 0 (axisSupportOfMask 27))) + (2 * (a 0 (axisSupportOfMask 28))) + ((-2) * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 3) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_3_0,
    maskKrawtchoukCoeff_3_1,
    maskKrawtchoukCoeff_3_2,
    maskKrawtchoukCoeff_3_3,
    maskKrawtchoukCoeff_3_4,
    maskKrawtchoukCoeff_3_5,
    maskKrawtchoukCoeff_3_6,
    maskKrawtchoukCoeff_3_7,
    maskKrawtchoukCoeff_3_8,
    maskKrawtchoukCoeff_3_9,
    maskKrawtchoukCoeff_3_10,
    maskKrawtchoukCoeff_3_11,
    maskKrawtchoukCoeff_3_12,
    maskKrawtchoukCoeff_3_13,
    maskKrawtchoukCoeff_3_14,
    maskKrawtchoukCoeff_3_15,
    maskKrawtchoukCoeff_3_16,
    maskKrawtchoukCoeff_3_17,
    maskKrawtchoukCoeff_3_18,
    maskKrawtchoukCoeff_3_19,
    maskKrawtchoukCoeff_3_20,
    maskKrawtchoukCoeff_3_21,
    maskKrawtchoukCoeff_3_22,
    maskKrawtchoukCoeff_3_23,
    maskKrawtchoukCoeff_3_24,
    maskKrawtchoukCoeff_3_25,
    maskKrawtchoukCoeff_3_26,
    maskKrawtchoukCoeff_3_27,
    maskKrawtchoukCoeff_3_28,
    maskKrawtchoukCoeff_3_29,
    maskKrawtchoukCoeff_3_30,
    maskKrawtchoukCoeff_3_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 8; source assertion 167. -/
theorem k242CorePremise8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((4 * (a 0 (axisSupportOfMask 0))) + ((-4) * (a 0 (axisSupportOfMask 1))) + (4 * (a 0 (axisSupportOfMask 2))) + ((-4) * (a 0 (axisSupportOfMask 3))) + ((-1) * (a 0 (axisSupportOfMask 4))) + (1 * (a 0 (axisSupportOfMask 5))) + ((-1) * (a 0 (axisSupportOfMask 6))) + (1 * (a 0 (axisSupportOfMask 7))) + (4 * (a 0 (axisSupportOfMask 8))) + ((-4) * (a 0 (axisSupportOfMask 9))) + (4 * (a 0 (axisSupportOfMask 10))) + ((-4) * (a 0 (axisSupportOfMask 11))) + ((-1) * (a 0 (axisSupportOfMask 12))) + (1 * (a 0 (axisSupportOfMask 13))) + ((-1) * (a 0 (axisSupportOfMask 14))) + (1 * (a 0 (axisSupportOfMask 15))) + (4 * (a 0 (axisSupportOfMask 16))) + ((-4) * (a 0 (axisSupportOfMask 17))) + (4 * (a 0 (axisSupportOfMask 18))) + ((-4) * (a 0 (axisSupportOfMask 19))) + ((-1) * (a 0 (axisSupportOfMask 20))) + (1 * (a 0 (axisSupportOfMask 21))) + ((-1) * (a 0 (axisSupportOfMask 22))) + (1 * (a 0 (axisSupportOfMask 23))) + (4 * (a 0 (axisSupportOfMask 24))) + ((-4) * (a 0 (axisSupportOfMask 25))) + (4 * (a 0 (axisSupportOfMask 26))) + ((-4) * (a 0 (axisSupportOfMask 27))) + ((-1) * (a 0 (axisSupportOfMask 28))) + (1 * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 5) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_5_0,
    maskKrawtchoukCoeff_5_1,
    maskKrawtchoukCoeff_5_2,
    maskKrawtchoukCoeff_5_3,
    maskKrawtchoukCoeff_5_4,
    maskKrawtchoukCoeff_5_5,
    maskKrawtchoukCoeff_5_6,
    maskKrawtchoukCoeff_5_7,
    maskKrawtchoukCoeff_5_8,
    maskKrawtchoukCoeff_5_9,
    maskKrawtchoukCoeff_5_10,
    maskKrawtchoukCoeff_5_11,
    maskKrawtchoukCoeff_5_12,
    maskKrawtchoukCoeff_5_13,
    maskKrawtchoukCoeff_5_14,
    maskKrawtchoukCoeff_5_15,
    maskKrawtchoukCoeff_5_16,
    maskKrawtchoukCoeff_5_17,
    maskKrawtchoukCoeff_5_18,
    maskKrawtchoukCoeff_5_19,
    maskKrawtchoukCoeff_5_20,
    maskKrawtchoukCoeff_5_21,
    maskKrawtchoukCoeff_5_22,
    maskKrawtchoukCoeff_5_23,
    maskKrawtchoukCoeff_5_24,
    maskKrawtchoukCoeff_5_25,
    maskKrawtchoukCoeff_5_26,
    maskKrawtchoukCoeff_5_27,
    maskKrawtchoukCoeff_5_28,
    maskKrawtchoukCoeff_5_29,
    maskKrawtchoukCoeff_5_30,
    maskKrawtchoukCoeff_5_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 9; source assertion 169. -/
theorem k242CorePremise9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((8 * (a 0 (axisSupportOfMask 0))) + (8 * (a 0 (axisSupportOfMask 1))) + ((-4) * (a 0 (axisSupportOfMask 2))) + ((-4) * (a 0 (axisSupportOfMask 3))) + ((-2) * (a 0 (axisSupportOfMask 4))) + ((-2) * (a 0 (axisSupportOfMask 5))) + (1 * (a 0 (axisSupportOfMask 6))) + (1 * (a 0 (axisSupportOfMask 7))) + (8 * (a 0 (axisSupportOfMask 8))) + (8 * (a 0 (axisSupportOfMask 9))) + ((-4) * (a 0 (axisSupportOfMask 10))) + ((-4) * (a 0 (axisSupportOfMask 11))) + ((-2) * (a 0 (axisSupportOfMask 12))) + ((-2) * (a 0 (axisSupportOfMask 13))) + (1 * (a 0 (axisSupportOfMask 14))) + (1 * (a 0 (axisSupportOfMask 15))) + (8 * (a 0 (axisSupportOfMask 16))) + (8 * (a 0 (axisSupportOfMask 17))) + ((-4) * (a 0 (axisSupportOfMask 18))) + ((-4) * (a 0 (axisSupportOfMask 19))) + ((-2) * (a 0 (axisSupportOfMask 20))) + ((-2) * (a 0 (axisSupportOfMask 21))) + (1 * (a 0 (axisSupportOfMask 22))) + (1 * (a 0 (axisSupportOfMask 23))) + (8 * (a 0 (axisSupportOfMask 24))) + (8 * (a 0 (axisSupportOfMask 25))) + ((-4) * (a 0 (axisSupportOfMask 26))) + ((-4) * (a 0 (axisSupportOfMask 27))) + ((-2) * (a 0 (axisSupportOfMask 28))) + ((-2) * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 6) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_6_0,
    maskKrawtchoukCoeff_6_1,
    maskKrawtchoukCoeff_6_2,
    maskKrawtchoukCoeff_6_3,
    maskKrawtchoukCoeff_6_4,
    maskKrawtchoukCoeff_6_5,
    maskKrawtchoukCoeff_6_6,
    maskKrawtchoukCoeff_6_7,
    maskKrawtchoukCoeff_6_8,
    maskKrawtchoukCoeff_6_9,
    maskKrawtchoukCoeff_6_10,
    maskKrawtchoukCoeff_6_11,
    maskKrawtchoukCoeff_6_12,
    maskKrawtchoukCoeff_6_13,
    maskKrawtchoukCoeff_6_14,
    maskKrawtchoukCoeff_6_15,
    maskKrawtchoukCoeff_6_16,
    maskKrawtchoukCoeff_6_17,
    maskKrawtchoukCoeff_6_18,
    maskKrawtchoukCoeff_6_19,
    maskKrawtchoukCoeff_6_20,
    maskKrawtchoukCoeff_6_21,
    maskKrawtchoukCoeff_6_22,
    maskKrawtchoukCoeff_6_23,
    maskKrawtchoukCoeff_6_24,
    maskKrawtchoukCoeff_6_25,
    maskKrawtchoukCoeff_6_26,
    maskKrawtchoukCoeff_6_27,
    maskKrawtchoukCoeff_6_28,
    maskKrawtchoukCoeff_6_29,
    maskKrawtchoukCoeff_6_30,
    maskKrawtchoukCoeff_6_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

end Fuglede
