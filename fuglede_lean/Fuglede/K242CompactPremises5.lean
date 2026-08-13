import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 5. -/

namespace Fuglede

/-- Core premise 50; source assertion 441. -/
theorem k242CorePremise50
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((80 * (a 1 (axisSupportOfMask 0))) + (80 * (a 1 (axisSupportOfMask 1))) + ((-40) * (a 1 (axisSupportOfMask 2))) + ((-40) * (a 1 (axisSupportOfMask 3))) + ((-20) * (a 1 (axisSupportOfMask 4))) + ((-20) * (a 1 (axisSupportOfMask 5))) + (10 * (a 1 (axisSupportOfMask 6))) + (10 * (a 1 (axisSupportOfMask 7))) + (80 * (a 1 (axisSupportOfMask 8))) + (80 * (a 1 (axisSupportOfMask 9))) + ((-40) * (a 1 (axisSupportOfMask 10))) + ((-40) * (a 1 (axisSupportOfMask 11))) + ((-20) * (a 1 (axisSupportOfMask 12))) + ((-20) * (a 1 (axisSupportOfMask 13))) + (10 * (a 1 (axisSupportOfMask 14))) + (10 * (a 1 (axisSupportOfMask 15))) + ((-8) * (a 1 (axisSupportOfMask 16))) + ((-8) * (a 1 (axisSupportOfMask 17))) + (4 * (a 1 (axisSupportOfMask 18))) + (4 * (a 1 (axisSupportOfMask 19))) + (2 * (a 1 (axisSupportOfMask 20))) + (2 * (a 1 (axisSupportOfMask 21))) + ((-1) * (a 1 (axisSupportOfMask 22))) + ((-1) * (a 1 (axisSupportOfMask 23))) + ((-8) * (a 1 (axisSupportOfMask 24))) + ((-8) * (a 1 (axisSupportOfMask 25))) + (4 * (a 1 (axisSupportOfMask 26))) + (4 * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + (2 * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 22) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_22_0,
    maskKrawtchoukCoeff_22_1,
    maskKrawtchoukCoeff_22_2,
    maskKrawtchoukCoeff_22_3,
    maskKrawtchoukCoeff_22_4,
    maskKrawtchoukCoeff_22_5,
    maskKrawtchoukCoeff_22_6,
    maskKrawtchoukCoeff_22_7,
    maskKrawtchoukCoeff_22_8,
    maskKrawtchoukCoeff_22_9,
    maskKrawtchoukCoeff_22_10,
    maskKrawtchoukCoeff_22_11,
    maskKrawtchoukCoeff_22_12,
    maskKrawtchoukCoeff_22_13,
    maskKrawtchoukCoeff_22_14,
    maskKrawtchoukCoeff_22_15,
    maskKrawtchoukCoeff_22_16,
    maskKrawtchoukCoeff_22_17,
    maskKrawtchoukCoeff_22_18,
    maskKrawtchoukCoeff_22_19,
    maskKrawtchoukCoeff_22_20,
    maskKrawtchoukCoeff_22_21,
    maskKrawtchoukCoeff_22_22,
    maskKrawtchoukCoeff_22_23,
    maskKrawtchoukCoeff_22_24,
    maskKrawtchoukCoeff_22_25,
    maskKrawtchoukCoeff_22_26,
    maskKrawtchoukCoeff_22_27,
    maskKrawtchoukCoeff_22_28,
    maskKrawtchoukCoeff_22_29,
    maskKrawtchoukCoeff_22_30,
    maskKrawtchoukCoeff_22_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 51; source assertion 443. -/
theorem k242CorePremise51
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((80 * (a 1 (axisSupportOfMask 0))) + ((-80) * (a 1 (axisSupportOfMask 1))) + ((-40) * (a 1 (axisSupportOfMask 2))) + (40 * (a 1 (axisSupportOfMask 3))) + ((-20) * (a 1 (axisSupportOfMask 4))) + (20 * (a 1 (axisSupportOfMask 5))) + (10 * (a 1 (axisSupportOfMask 6))) + ((-10) * (a 1 (axisSupportOfMask 7))) + (80 * (a 1 (axisSupportOfMask 8))) + ((-80) * (a 1 (axisSupportOfMask 9))) + ((-40) * (a 1 (axisSupportOfMask 10))) + (40 * (a 1 (axisSupportOfMask 11))) + ((-20) * (a 1 (axisSupportOfMask 12))) + (20 * (a 1 (axisSupportOfMask 13))) + (10 * (a 1 (axisSupportOfMask 14))) + ((-10) * (a 1 (axisSupportOfMask 15))) + ((-8) * (a 1 (axisSupportOfMask 16))) + (8 * (a 1 (axisSupportOfMask 17))) + (4 * (a 1 (axisSupportOfMask 18))) + ((-4) * (a 1 (axisSupportOfMask 19))) + (2 * (a 1 (axisSupportOfMask 20))) + ((-2) * (a 1 (axisSupportOfMask 21))) + ((-1) * (a 1 (axisSupportOfMask 22))) + (1 * (a 1 (axisSupportOfMask 23))) + ((-8) * (a 1 (axisSupportOfMask 24))) + (8 * (a 1 (axisSupportOfMask 25))) + (4 * (a 1 (axisSupportOfMask 26))) + ((-4) * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 23) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_23_0,
    maskKrawtchoukCoeff_23_1,
    maskKrawtchoukCoeff_23_2,
    maskKrawtchoukCoeff_23_3,
    maskKrawtchoukCoeff_23_4,
    maskKrawtchoukCoeff_23_5,
    maskKrawtchoukCoeff_23_6,
    maskKrawtchoukCoeff_23_7,
    maskKrawtchoukCoeff_23_8,
    maskKrawtchoukCoeff_23_9,
    maskKrawtchoukCoeff_23_10,
    maskKrawtchoukCoeff_23_11,
    maskKrawtchoukCoeff_23_12,
    maskKrawtchoukCoeff_23_13,
    maskKrawtchoukCoeff_23_14,
    maskKrawtchoukCoeff_23_15,
    maskKrawtchoukCoeff_23_16,
    maskKrawtchoukCoeff_23_17,
    maskKrawtchoukCoeff_23_18,
    maskKrawtchoukCoeff_23_19,
    maskKrawtchoukCoeff_23_20,
    maskKrawtchoukCoeff_23_21,
    maskKrawtchoukCoeff_23_22,
    maskKrawtchoukCoeff_23_23,
    maskKrawtchoukCoeff_23_24,
    maskKrawtchoukCoeff_23_25,
    maskKrawtchoukCoeff_23_26,
    maskKrawtchoukCoeff_23_27,
    maskKrawtchoukCoeff_23_28,
    maskKrawtchoukCoeff_23_29,
    maskKrawtchoukCoeff_23_30,
    maskKrawtchoukCoeff_23_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 52; source assertion 445. -/
theorem k242CorePremise52
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((60 * (a 1 (axisSupportOfMask 0))) + (60 * (a 1 (axisSupportOfMask 1))) + (60 * (a 1 (axisSupportOfMask 2))) + (60 * (a 1 (axisSupportOfMask 3))) + (60 * (a 1 (axisSupportOfMask 4))) + (60 * (a 1 (axisSupportOfMask 5))) + (60 * (a 1 (axisSupportOfMask 6))) + (60 * (a 1 (axisSupportOfMask 7))) + ((-10) * (a 1 (axisSupportOfMask 8))) + ((-10) * (a 1 (axisSupportOfMask 9))) + ((-10) * (a 1 (axisSupportOfMask 10))) + ((-10) * (a 1 (axisSupportOfMask 11))) + ((-10) * (a 1 (axisSupportOfMask 12))) + ((-10) * (a 1 (axisSupportOfMask 13))) + ((-10) * (a 1 (axisSupportOfMask 14))) + ((-10) * (a 1 (axisSupportOfMask 15))) + ((-6) * (a 1 (axisSupportOfMask 16))) + ((-6) * (a 1 (axisSupportOfMask 17))) + ((-6) * (a 1 (axisSupportOfMask 18))) + ((-6) * (a 1 (axisSupportOfMask 19))) + ((-6) * (a 1 (axisSupportOfMask 20))) + ((-6) * (a 1 (axisSupportOfMask 21))) + ((-6) * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + (1 * (a 1 (axisSupportOfMask 24))) + (1 * (a 1 (axisSupportOfMask 25))) + (1 * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + (1 * (a 1 (axisSupportOfMask 28))) + (1 * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 24) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_24_0,
    maskKrawtchoukCoeff_24_1,
    maskKrawtchoukCoeff_24_2,
    maskKrawtchoukCoeff_24_3,
    maskKrawtchoukCoeff_24_4,
    maskKrawtchoukCoeff_24_5,
    maskKrawtchoukCoeff_24_6,
    maskKrawtchoukCoeff_24_7,
    maskKrawtchoukCoeff_24_8,
    maskKrawtchoukCoeff_24_9,
    maskKrawtchoukCoeff_24_10,
    maskKrawtchoukCoeff_24_11,
    maskKrawtchoukCoeff_24_12,
    maskKrawtchoukCoeff_24_13,
    maskKrawtchoukCoeff_24_14,
    maskKrawtchoukCoeff_24_15,
    maskKrawtchoukCoeff_24_16,
    maskKrawtchoukCoeff_24_17,
    maskKrawtchoukCoeff_24_18,
    maskKrawtchoukCoeff_24_19,
    maskKrawtchoukCoeff_24_20,
    maskKrawtchoukCoeff_24_21,
    maskKrawtchoukCoeff_24_22,
    maskKrawtchoukCoeff_24_23,
    maskKrawtchoukCoeff_24_24,
    maskKrawtchoukCoeff_24_25,
    maskKrawtchoukCoeff_24_26,
    maskKrawtchoukCoeff_24_27,
    maskKrawtchoukCoeff_24_28,
    maskKrawtchoukCoeff_24_29,
    maskKrawtchoukCoeff_24_30,
    maskKrawtchoukCoeff_24_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 53; source assertion 447. -/
theorem k242CorePremise53
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((60 * (a 1 (axisSupportOfMask 0))) + ((-60) * (a 1 (axisSupportOfMask 1))) + (60 * (a 1 (axisSupportOfMask 2))) + ((-60) * (a 1 (axisSupportOfMask 3))) + (60 * (a 1 (axisSupportOfMask 4))) + ((-60) * (a 1 (axisSupportOfMask 5))) + (60 * (a 1 (axisSupportOfMask 6))) + ((-60) * (a 1 (axisSupportOfMask 7))) + ((-10) * (a 1 (axisSupportOfMask 8))) + (10 * (a 1 (axisSupportOfMask 9))) + ((-10) * (a 1 (axisSupportOfMask 10))) + (10 * (a 1 (axisSupportOfMask 11))) + ((-10) * (a 1 (axisSupportOfMask 12))) + (10 * (a 1 (axisSupportOfMask 13))) + ((-10) * (a 1 (axisSupportOfMask 14))) + (10 * (a 1 (axisSupportOfMask 15))) + ((-6) * (a 1 (axisSupportOfMask 16))) + (6 * (a 1 (axisSupportOfMask 17))) + ((-6) * (a 1 (axisSupportOfMask 18))) + (6 * (a 1 (axisSupportOfMask 19))) + ((-6) * (a 1 (axisSupportOfMask 20))) + (6 * (a 1 (axisSupportOfMask 21))) + ((-6) * (a 1 (axisSupportOfMask 22))) + (6 * (a 1 (axisSupportOfMask 23))) + (1 * (a 1 (axisSupportOfMask 24))) + ((-1) * (a 1 (axisSupportOfMask 25))) + (1 * (a 1 (axisSupportOfMask 26))) + ((-1) * (a 1 (axisSupportOfMask 27))) + (1 * (a 1 (axisSupportOfMask 28))) + ((-1) * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 25) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_25_0,
    maskKrawtchoukCoeff_25_1,
    maskKrawtchoukCoeff_25_2,
    maskKrawtchoukCoeff_25_3,
    maskKrawtchoukCoeff_25_4,
    maskKrawtchoukCoeff_25_5,
    maskKrawtchoukCoeff_25_6,
    maskKrawtchoukCoeff_25_7,
    maskKrawtchoukCoeff_25_8,
    maskKrawtchoukCoeff_25_9,
    maskKrawtchoukCoeff_25_10,
    maskKrawtchoukCoeff_25_11,
    maskKrawtchoukCoeff_25_12,
    maskKrawtchoukCoeff_25_13,
    maskKrawtchoukCoeff_25_14,
    maskKrawtchoukCoeff_25_15,
    maskKrawtchoukCoeff_25_16,
    maskKrawtchoukCoeff_25_17,
    maskKrawtchoukCoeff_25_18,
    maskKrawtchoukCoeff_25_19,
    maskKrawtchoukCoeff_25_20,
    maskKrawtchoukCoeff_25_21,
    maskKrawtchoukCoeff_25_22,
    maskKrawtchoukCoeff_25_23,
    maskKrawtchoukCoeff_25_24,
    maskKrawtchoukCoeff_25_25,
    maskKrawtchoukCoeff_25_26,
    maskKrawtchoukCoeff_25_27,
    maskKrawtchoukCoeff_25_28,
    maskKrawtchoukCoeff_25_29,
    maskKrawtchoukCoeff_25_30,
    maskKrawtchoukCoeff_25_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 54; source assertion 449. -/
theorem k242CorePremise54
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((120 * (a 1 (axisSupportOfMask 0))) + (120 * (a 1 (axisSupportOfMask 1))) + ((-60) * (a 1 (axisSupportOfMask 2))) + ((-60) * (a 1 (axisSupportOfMask 3))) + (120 * (a 1 (axisSupportOfMask 4))) + (120 * (a 1 (axisSupportOfMask 5))) + ((-60) * (a 1 (axisSupportOfMask 6))) + ((-60) * (a 1 (axisSupportOfMask 7))) + ((-20) * (a 1 (axisSupportOfMask 8))) + ((-20) * (a 1 (axisSupportOfMask 9))) + (10 * (a 1 (axisSupportOfMask 10))) + (10 * (a 1 (axisSupportOfMask 11))) + ((-20) * (a 1 (axisSupportOfMask 12))) + ((-20) * (a 1 (axisSupportOfMask 13))) + (10 * (a 1 (axisSupportOfMask 14))) + (10 * (a 1 (axisSupportOfMask 15))) + ((-12) * (a 1 (axisSupportOfMask 16))) + ((-12) * (a 1 (axisSupportOfMask 17))) + (6 * (a 1 (axisSupportOfMask 18))) + (6 * (a 1 (axisSupportOfMask 19))) + ((-12) * (a 1 (axisSupportOfMask 20))) + ((-12) * (a 1 (axisSupportOfMask 21))) + (6 * (a 1 (axisSupportOfMask 22))) + (6 * (a 1 (axisSupportOfMask 23))) + (2 * (a 1 (axisSupportOfMask 24))) + (2 * (a 1 (axisSupportOfMask 25))) + ((-1) * (a 1 (axisSupportOfMask 26))) + ((-1) * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + (2 * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 26) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_26_0,
    maskKrawtchoukCoeff_26_1,
    maskKrawtchoukCoeff_26_2,
    maskKrawtchoukCoeff_26_3,
    maskKrawtchoukCoeff_26_4,
    maskKrawtchoukCoeff_26_5,
    maskKrawtchoukCoeff_26_6,
    maskKrawtchoukCoeff_26_7,
    maskKrawtchoukCoeff_26_8,
    maskKrawtchoukCoeff_26_9,
    maskKrawtchoukCoeff_26_10,
    maskKrawtchoukCoeff_26_11,
    maskKrawtchoukCoeff_26_12,
    maskKrawtchoukCoeff_26_13,
    maskKrawtchoukCoeff_26_14,
    maskKrawtchoukCoeff_26_15,
    maskKrawtchoukCoeff_26_16,
    maskKrawtchoukCoeff_26_17,
    maskKrawtchoukCoeff_26_18,
    maskKrawtchoukCoeff_26_19,
    maskKrawtchoukCoeff_26_20,
    maskKrawtchoukCoeff_26_21,
    maskKrawtchoukCoeff_26_22,
    maskKrawtchoukCoeff_26_23,
    maskKrawtchoukCoeff_26_24,
    maskKrawtchoukCoeff_26_25,
    maskKrawtchoukCoeff_26_26,
    maskKrawtchoukCoeff_26_27,
    maskKrawtchoukCoeff_26_28,
    maskKrawtchoukCoeff_26_29,
    maskKrawtchoukCoeff_26_30,
    maskKrawtchoukCoeff_26_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 55; source assertion 451. -/
theorem k242CorePremise55
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((120 * (a 1 (axisSupportOfMask 0))) + ((-120) * (a 1 (axisSupportOfMask 1))) + ((-60) * (a 1 (axisSupportOfMask 2))) + (60 * (a 1 (axisSupportOfMask 3))) + (120 * (a 1 (axisSupportOfMask 4))) + ((-120) * (a 1 (axisSupportOfMask 5))) + ((-60) * (a 1 (axisSupportOfMask 6))) + (60 * (a 1 (axisSupportOfMask 7))) + ((-20) * (a 1 (axisSupportOfMask 8))) + (20 * (a 1 (axisSupportOfMask 9))) + (10 * (a 1 (axisSupportOfMask 10))) + ((-10) * (a 1 (axisSupportOfMask 11))) + ((-20) * (a 1 (axisSupportOfMask 12))) + (20 * (a 1 (axisSupportOfMask 13))) + (10 * (a 1 (axisSupportOfMask 14))) + ((-10) * (a 1 (axisSupportOfMask 15))) + ((-12) * (a 1 (axisSupportOfMask 16))) + (12 * (a 1 (axisSupportOfMask 17))) + (6 * (a 1 (axisSupportOfMask 18))) + ((-6) * (a 1 (axisSupportOfMask 19))) + ((-12) * (a 1 (axisSupportOfMask 20))) + (12 * (a 1 (axisSupportOfMask 21))) + (6 * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + (2 * (a 1 (axisSupportOfMask 24))) + ((-2) * (a 1 (axisSupportOfMask 25))) + ((-1) * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 27) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_27_0,
    maskKrawtchoukCoeff_27_1,
    maskKrawtchoukCoeff_27_2,
    maskKrawtchoukCoeff_27_3,
    maskKrawtchoukCoeff_27_4,
    maskKrawtchoukCoeff_27_5,
    maskKrawtchoukCoeff_27_6,
    maskKrawtchoukCoeff_27_7,
    maskKrawtchoukCoeff_27_8,
    maskKrawtchoukCoeff_27_9,
    maskKrawtchoukCoeff_27_10,
    maskKrawtchoukCoeff_27_11,
    maskKrawtchoukCoeff_27_12,
    maskKrawtchoukCoeff_27_13,
    maskKrawtchoukCoeff_27_14,
    maskKrawtchoukCoeff_27_15,
    maskKrawtchoukCoeff_27_16,
    maskKrawtchoukCoeff_27_17,
    maskKrawtchoukCoeff_27_18,
    maskKrawtchoukCoeff_27_19,
    maskKrawtchoukCoeff_27_20,
    maskKrawtchoukCoeff_27_21,
    maskKrawtchoukCoeff_27_22,
    maskKrawtchoukCoeff_27_23,
    maskKrawtchoukCoeff_27_24,
    maskKrawtchoukCoeff_27_25,
    maskKrawtchoukCoeff_27_26,
    maskKrawtchoukCoeff_27_27,
    maskKrawtchoukCoeff_27_28,
    maskKrawtchoukCoeff_27_29,
    maskKrawtchoukCoeff_27_30,
    maskKrawtchoukCoeff_27_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 56; source assertion 462. -/
theorem k242CorePremise56
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 2)) = 0) := by
  have hp := hconstraints.prime_exclusion 1 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 57; source assertion 464. -/
theorem k242CorePremise57
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 4)) = 0) := by
  have hp := hconstraints.prime_exclusion 1 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 58; source assertion 466. -/
theorem k242CorePremise58
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 8)) = 0) := by
  have hp := hconstraints.prime_exclusion 1 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 59; source assertion 491. -/
theorem k242CorePremise59
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((a 1 (axisSupportOfMask 6)) > 0) → (z 0 (axisSupportOfMask 6))) := by
  intro hpositive
  exact hconstraints.cross_spectrum_to_set (axisSupportOfMask 6) (by decide) hpositive

end Fuglede
