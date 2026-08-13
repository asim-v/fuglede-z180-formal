import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 1. -/

namespace Fuglede

/-- Core premise 10; source assertion 171. -/
theorem k242CorePremise10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((8 * (a 0 (axisSupportOfMask 0))) + ((-8) * (a 0 (axisSupportOfMask 1))) + ((-4) * (a 0 (axisSupportOfMask 2))) + (4 * (a 0 (axisSupportOfMask 3))) + ((-2) * (a 0 (axisSupportOfMask 4))) + (2 * (a 0 (axisSupportOfMask 5))) + (1 * (a 0 (axisSupportOfMask 6))) + ((-1) * (a 0 (axisSupportOfMask 7))) + (8 * (a 0 (axisSupportOfMask 8))) + ((-8) * (a 0 (axisSupportOfMask 9))) + ((-4) * (a 0 (axisSupportOfMask 10))) + (4 * (a 0 (axisSupportOfMask 11))) + ((-2) * (a 0 (axisSupportOfMask 12))) + (2 * (a 0 (axisSupportOfMask 13))) + (1 * (a 0 (axisSupportOfMask 14))) + ((-1) * (a 0 (axisSupportOfMask 15))) + (8 * (a 0 (axisSupportOfMask 16))) + ((-8) * (a 0 (axisSupportOfMask 17))) + ((-4) * (a 0 (axisSupportOfMask 18))) + (4 * (a 0 (axisSupportOfMask 19))) + ((-2) * (a 0 (axisSupportOfMask 20))) + (2 * (a 0 (axisSupportOfMask 21))) + (1 * (a 0 (axisSupportOfMask 22))) + ((-1) * (a 0 (axisSupportOfMask 23))) + (8 * (a 0 (axisSupportOfMask 24))) + ((-8) * (a 0 (axisSupportOfMask 25))) + ((-4) * (a 0 (axisSupportOfMask 26))) + (4 * (a 0 (axisSupportOfMask 27))) + ((-2) * (a 0 (axisSupportOfMask 28))) + (2 * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 7) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_7_0,
    maskKrawtchoukCoeff_7_1,
    maskKrawtchoukCoeff_7_2,
    maskKrawtchoukCoeff_7_3,
    maskKrawtchoukCoeff_7_4,
    maskKrawtchoukCoeff_7_5,
    maskKrawtchoukCoeff_7_6,
    maskKrawtchoukCoeff_7_7,
    maskKrawtchoukCoeff_7_8,
    maskKrawtchoukCoeff_7_9,
    maskKrawtchoukCoeff_7_10,
    maskKrawtchoukCoeff_7_11,
    maskKrawtchoukCoeff_7_12,
    maskKrawtchoukCoeff_7_13,
    maskKrawtchoukCoeff_7_14,
    maskKrawtchoukCoeff_7_15,
    maskKrawtchoukCoeff_7_16,
    maskKrawtchoukCoeff_7_17,
    maskKrawtchoukCoeff_7_18,
    maskKrawtchoukCoeff_7_19,
    maskKrawtchoukCoeff_7_20,
    maskKrawtchoukCoeff_7_21,
    maskKrawtchoukCoeff_7_22,
    maskKrawtchoukCoeff_7_23,
    maskKrawtchoukCoeff_7_24,
    maskKrawtchoukCoeff_7_25,
    maskKrawtchoukCoeff_7_26,
    maskKrawtchoukCoeff_7_27,
    maskKrawtchoukCoeff_7_28,
    maskKrawtchoukCoeff_7_29,
    maskKrawtchoukCoeff_7_30,
    maskKrawtchoukCoeff_7_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 11; source assertion 175. -/
theorem k242CorePremise11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((6 * (a 0 (axisSupportOfMask 0))) + ((-6) * (a 0 (axisSupportOfMask 1))) + (6 * (a 0 (axisSupportOfMask 2))) + ((-6) * (a 0 (axisSupportOfMask 3))) + (6 * (a 0 (axisSupportOfMask 4))) + ((-6) * (a 0 (axisSupportOfMask 5))) + (6 * (a 0 (axisSupportOfMask 6))) + ((-6) * (a 0 (axisSupportOfMask 7))) + ((-1) * (a 0 (axisSupportOfMask 8))) + (1 * (a 0 (axisSupportOfMask 9))) + ((-1) * (a 0 (axisSupportOfMask 10))) + (1 * (a 0 (axisSupportOfMask 11))) + ((-1) * (a 0 (axisSupportOfMask 12))) + (1 * (a 0 (axisSupportOfMask 13))) + ((-1) * (a 0 (axisSupportOfMask 14))) + (1 * (a 0 (axisSupportOfMask 15))) + (6 * (a 0 (axisSupportOfMask 16))) + ((-6) * (a 0 (axisSupportOfMask 17))) + (6 * (a 0 (axisSupportOfMask 18))) + ((-6) * (a 0 (axisSupportOfMask 19))) + (6 * (a 0 (axisSupportOfMask 20))) + ((-6) * (a 0 (axisSupportOfMask 21))) + (6 * (a 0 (axisSupportOfMask 22))) + ((-6) * (a 0 (axisSupportOfMask 23))) + ((-1) * (a 0 (axisSupportOfMask 24))) + (1 * (a 0 (axisSupportOfMask 25))) + ((-1) * (a 0 (axisSupportOfMask 26))) + (1 * (a 0 (axisSupportOfMask 27))) + ((-1) * (a 0 (axisSupportOfMask 28))) + (1 * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 9) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_9_0,
    maskKrawtchoukCoeff_9_1,
    maskKrawtchoukCoeff_9_2,
    maskKrawtchoukCoeff_9_3,
    maskKrawtchoukCoeff_9_4,
    maskKrawtchoukCoeff_9_5,
    maskKrawtchoukCoeff_9_6,
    maskKrawtchoukCoeff_9_7,
    maskKrawtchoukCoeff_9_8,
    maskKrawtchoukCoeff_9_9,
    maskKrawtchoukCoeff_9_10,
    maskKrawtchoukCoeff_9_11,
    maskKrawtchoukCoeff_9_12,
    maskKrawtchoukCoeff_9_13,
    maskKrawtchoukCoeff_9_14,
    maskKrawtchoukCoeff_9_15,
    maskKrawtchoukCoeff_9_16,
    maskKrawtchoukCoeff_9_17,
    maskKrawtchoukCoeff_9_18,
    maskKrawtchoukCoeff_9_19,
    maskKrawtchoukCoeff_9_20,
    maskKrawtchoukCoeff_9_21,
    maskKrawtchoukCoeff_9_22,
    maskKrawtchoukCoeff_9_23,
    maskKrawtchoukCoeff_9_24,
    maskKrawtchoukCoeff_9_25,
    maskKrawtchoukCoeff_9_26,
    maskKrawtchoukCoeff_9_27,
    maskKrawtchoukCoeff_9_28,
    maskKrawtchoukCoeff_9_29,
    maskKrawtchoukCoeff_9_30,
    maskKrawtchoukCoeff_9_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 12; source assertion 177. -/
theorem k242CorePremise12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((12 * (a 0 (axisSupportOfMask 0))) + (12 * (a 0 (axisSupportOfMask 1))) + ((-6) * (a 0 (axisSupportOfMask 2))) + ((-6) * (a 0 (axisSupportOfMask 3))) + (12 * (a 0 (axisSupportOfMask 4))) + (12 * (a 0 (axisSupportOfMask 5))) + ((-6) * (a 0 (axisSupportOfMask 6))) + ((-6) * (a 0 (axisSupportOfMask 7))) + ((-2) * (a 0 (axisSupportOfMask 8))) + ((-2) * (a 0 (axisSupportOfMask 9))) + (1 * (a 0 (axisSupportOfMask 10))) + (1 * (a 0 (axisSupportOfMask 11))) + ((-2) * (a 0 (axisSupportOfMask 12))) + ((-2) * (a 0 (axisSupportOfMask 13))) + (1 * (a 0 (axisSupportOfMask 14))) + (1 * (a 0 (axisSupportOfMask 15))) + (12 * (a 0 (axisSupportOfMask 16))) + (12 * (a 0 (axisSupportOfMask 17))) + ((-6) * (a 0 (axisSupportOfMask 18))) + ((-6) * (a 0 (axisSupportOfMask 19))) + (12 * (a 0 (axisSupportOfMask 20))) + (12 * (a 0 (axisSupportOfMask 21))) + ((-6) * (a 0 (axisSupportOfMask 22))) + ((-6) * (a 0 (axisSupportOfMask 23))) + ((-2) * (a 0 (axisSupportOfMask 24))) + ((-2) * (a 0 (axisSupportOfMask 25))) + (1 * (a 0 (axisSupportOfMask 26))) + (1 * (a 0 (axisSupportOfMask 27))) + ((-2) * (a 0 (axisSupportOfMask 28))) + ((-2) * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 10) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_10_0,
    maskKrawtchoukCoeff_10_1,
    maskKrawtchoukCoeff_10_2,
    maskKrawtchoukCoeff_10_3,
    maskKrawtchoukCoeff_10_4,
    maskKrawtchoukCoeff_10_5,
    maskKrawtchoukCoeff_10_6,
    maskKrawtchoukCoeff_10_7,
    maskKrawtchoukCoeff_10_8,
    maskKrawtchoukCoeff_10_9,
    maskKrawtchoukCoeff_10_10,
    maskKrawtchoukCoeff_10_11,
    maskKrawtchoukCoeff_10_12,
    maskKrawtchoukCoeff_10_13,
    maskKrawtchoukCoeff_10_14,
    maskKrawtchoukCoeff_10_15,
    maskKrawtchoukCoeff_10_16,
    maskKrawtchoukCoeff_10_17,
    maskKrawtchoukCoeff_10_18,
    maskKrawtchoukCoeff_10_19,
    maskKrawtchoukCoeff_10_20,
    maskKrawtchoukCoeff_10_21,
    maskKrawtchoukCoeff_10_22,
    maskKrawtchoukCoeff_10_23,
    maskKrawtchoukCoeff_10_24,
    maskKrawtchoukCoeff_10_25,
    maskKrawtchoukCoeff_10_26,
    maskKrawtchoukCoeff_10_27,
    maskKrawtchoukCoeff_10_28,
    maskKrawtchoukCoeff_10_29,
    maskKrawtchoukCoeff_10_30,
    maskKrawtchoukCoeff_10_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 13; source assertion 179. -/
theorem k242CorePremise13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((12 * (a 0 (axisSupportOfMask 0))) + ((-12) * (a 0 (axisSupportOfMask 1))) + ((-6) * (a 0 (axisSupportOfMask 2))) + (6 * (a 0 (axisSupportOfMask 3))) + (12 * (a 0 (axisSupportOfMask 4))) + ((-12) * (a 0 (axisSupportOfMask 5))) + ((-6) * (a 0 (axisSupportOfMask 6))) + (6 * (a 0 (axisSupportOfMask 7))) + ((-2) * (a 0 (axisSupportOfMask 8))) + (2 * (a 0 (axisSupportOfMask 9))) + (1 * (a 0 (axisSupportOfMask 10))) + ((-1) * (a 0 (axisSupportOfMask 11))) + ((-2) * (a 0 (axisSupportOfMask 12))) + (2 * (a 0 (axisSupportOfMask 13))) + (1 * (a 0 (axisSupportOfMask 14))) + ((-1) * (a 0 (axisSupportOfMask 15))) + (12 * (a 0 (axisSupportOfMask 16))) + ((-12) * (a 0 (axisSupportOfMask 17))) + ((-6) * (a 0 (axisSupportOfMask 18))) + (6 * (a 0 (axisSupportOfMask 19))) + (12 * (a 0 (axisSupportOfMask 20))) + ((-12) * (a 0 (axisSupportOfMask 21))) + ((-6) * (a 0 (axisSupportOfMask 22))) + (6 * (a 0 (axisSupportOfMask 23))) + ((-2) * (a 0 (axisSupportOfMask 24))) + (2 * (a 0 (axisSupportOfMask 25))) + (1 * (a 0 (axisSupportOfMask 26))) + ((-1) * (a 0 (axisSupportOfMask 27))) + ((-2) * (a 0 (axisSupportOfMask 28))) + (2 * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 11) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_11_0,
    maskKrawtchoukCoeff_11_1,
    maskKrawtchoukCoeff_11_2,
    maskKrawtchoukCoeff_11_3,
    maskKrawtchoukCoeff_11_4,
    maskKrawtchoukCoeff_11_5,
    maskKrawtchoukCoeff_11_6,
    maskKrawtchoukCoeff_11_7,
    maskKrawtchoukCoeff_11_8,
    maskKrawtchoukCoeff_11_9,
    maskKrawtchoukCoeff_11_10,
    maskKrawtchoukCoeff_11_11,
    maskKrawtchoukCoeff_11_12,
    maskKrawtchoukCoeff_11_13,
    maskKrawtchoukCoeff_11_14,
    maskKrawtchoukCoeff_11_15,
    maskKrawtchoukCoeff_11_16,
    maskKrawtchoukCoeff_11_17,
    maskKrawtchoukCoeff_11_18,
    maskKrawtchoukCoeff_11_19,
    maskKrawtchoukCoeff_11_20,
    maskKrawtchoukCoeff_11_21,
    maskKrawtchoukCoeff_11_22,
    maskKrawtchoukCoeff_11_23,
    maskKrawtchoukCoeff_11_24,
    maskKrawtchoukCoeff_11_25,
    maskKrawtchoukCoeff_11_26,
    maskKrawtchoukCoeff_11_27,
    maskKrawtchoukCoeff_11_28,
    maskKrawtchoukCoeff_11_29,
    maskKrawtchoukCoeff_11_30,
    maskKrawtchoukCoeff_11_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 14; source assertion 195. -/
theorem k242CorePremise14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((20 * (a 0 (axisSupportOfMask 0))) + ((-20) * (a 0 (axisSupportOfMask 1))) + ((-10) * (a 0 (axisSupportOfMask 2))) + (10 * (a 0 (axisSupportOfMask 3))) + (20 * (a 0 (axisSupportOfMask 4))) + ((-20) * (a 0 (axisSupportOfMask 5))) + ((-10) * (a 0 (axisSupportOfMask 6))) + (10 * (a 0 (axisSupportOfMask 7))) + (20 * (a 0 (axisSupportOfMask 8))) + ((-20) * (a 0 (axisSupportOfMask 9))) + ((-10) * (a 0 (axisSupportOfMask 10))) + (10 * (a 0 (axisSupportOfMask 11))) + (20 * (a 0 (axisSupportOfMask 12))) + ((-20) * (a 0 (axisSupportOfMask 13))) + ((-10) * (a 0 (axisSupportOfMask 14))) + (10 * (a 0 (axisSupportOfMask 15))) + ((-2) * (a 0 (axisSupportOfMask 16))) + (2 * (a 0 (axisSupportOfMask 17))) + (1 * (a 0 (axisSupportOfMask 18))) + ((-1) * (a 0 (axisSupportOfMask 19))) + ((-2) * (a 0 (axisSupportOfMask 20))) + (2 * (a 0 (axisSupportOfMask 21))) + (1 * (a 0 (axisSupportOfMask 22))) + ((-1) * (a 0 (axisSupportOfMask 23))) + ((-2) * (a 0 (axisSupportOfMask 24))) + (2 * (a 0 (axisSupportOfMask 25))) + (1 * (a 0 (axisSupportOfMask 26))) + ((-1) * (a 0 (axisSupportOfMask 27))) + ((-2) * (a 0 (axisSupportOfMask 28))) + (2 * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 19) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_19_0,
    maskKrawtchoukCoeff_19_1,
    maskKrawtchoukCoeff_19_2,
    maskKrawtchoukCoeff_19_3,
    maskKrawtchoukCoeff_19_4,
    maskKrawtchoukCoeff_19_5,
    maskKrawtchoukCoeff_19_6,
    maskKrawtchoukCoeff_19_7,
    maskKrawtchoukCoeff_19_8,
    maskKrawtchoukCoeff_19_9,
    maskKrawtchoukCoeff_19_10,
    maskKrawtchoukCoeff_19_11,
    maskKrawtchoukCoeff_19_12,
    maskKrawtchoukCoeff_19_13,
    maskKrawtchoukCoeff_19_14,
    maskKrawtchoukCoeff_19_15,
    maskKrawtchoukCoeff_19_16,
    maskKrawtchoukCoeff_19_17,
    maskKrawtchoukCoeff_19_18,
    maskKrawtchoukCoeff_19_19,
    maskKrawtchoukCoeff_19_20,
    maskKrawtchoukCoeff_19_21,
    maskKrawtchoukCoeff_19_22,
    maskKrawtchoukCoeff_19_23,
    maskKrawtchoukCoeff_19_24,
    maskKrawtchoukCoeff_19_25,
    maskKrawtchoukCoeff_19_26,
    maskKrawtchoukCoeff_19_27,
    maskKrawtchoukCoeff_19_28,
    maskKrawtchoukCoeff_19_29,
    maskKrawtchoukCoeff_19_30,
    maskKrawtchoukCoeff_19_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 15; source assertion 199. -/
theorem k242CorePremise15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((40 * (a 0 (axisSupportOfMask 0))) + ((-40) * (a 0 (axisSupportOfMask 1))) + (40 * (a 0 (axisSupportOfMask 2))) + ((-40) * (a 0 (axisSupportOfMask 3))) + ((-10) * (a 0 (axisSupportOfMask 4))) + (10 * (a 0 (axisSupportOfMask 5))) + ((-10) * (a 0 (axisSupportOfMask 6))) + (10 * (a 0 (axisSupportOfMask 7))) + (40 * (a 0 (axisSupportOfMask 8))) + ((-40) * (a 0 (axisSupportOfMask 9))) + (40 * (a 0 (axisSupportOfMask 10))) + ((-40) * (a 0 (axisSupportOfMask 11))) + ((-10) * (a 0 (axisSupportOfMask 12))) + (10 * (a 0 (axisSupportOfMask 13))) + ((-10) * (a 0 (axisSupportOfMask 14))) + (10 * (a 0 (axisSupportOfMask 15))) + ((-4) * (a 0 (axisSupportOfMask 16))) + (4 * (a 0 (axisSupportOfMask 17))) + ((-4) * (a 0 (axisSupportOfMask 18))) + (4 * (a 0 (axisSupportOfMask 19))) + (1 * (a 0 (axisSupportOfMask 20))) + ((-1) * (a 0 (axisSupportOfMask 21))) + (1 * (a 0 (axisSupportOfMask 22))) + ((-1) * (a 0 (axisSupportOfMask 23))) + ((-4) * (a 0 (axisSupportOfMask 24))) + (4 * (a 0 (axisSupportOfMask 25))) + ((-4) * (a 0 (axisSupportOfMask 26))) + (4 * (a 0 (axisSupportOfMask 27))) + (1 * (a 0 (axisSupportOfMask 28))) + ((-1) * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 21) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_21_0,
    maskKrawtchoukCoeff_21_1,
    maskKrawtchoukCoeff_21_2,
    maskKrawtchoukCoeff_21_3,
    maskKrawtchoukCoeff_21_4,
    maskKrawtchoukCoeff_21_5,
    maskKrawtchoukCoeff_21_6,
    maskKrawtchoukCoeff_21_7,
    maskKrawtchoukCoeff_21_8,
    maskKrawtchoukCoeff_21_9,
    maskKrawtchoukCoeff_21_10,
    maskKrawtchoukCoeff_21_11,
    maskKrawtchoukCoeff_21_12,
    maskKrawtchoukCoeff_21_13,
    maskKrawtchoukCoeff_21_14,
    maskKrawtchoukCoeff_21_15,
    maskKrawtchoukCoeff_21_16,
    maskKrawtchoukCoeff_21_17,
    maskKrawtchoukCoeff_21_18,
    maskKrawtchoukCoeff_21_19,
    maskKrawtchoukCoeff_21_20,
    maskKrawtchoukCoeff_21_21,
    maskKrawtchoukCoeff_21_22,
    maskKrawtchoukCoeff_21_23,
    maskKrawtchoukCoeff_21_24,
    maskKrawtchoukCoeff_21_25,
    maskKrawtchoukCoeff_21_26,
    maskKrawtchoukCoeff_21_27,
    maskKrawtchoukCoeff_21_28,
    maskKrawtchoukCoeff_21_29,
    maskKrawtchoukCoeff_21_30,
    maskKrawtchoukCoeff_21_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 16; source assertion 201. -/
theorem k242CorePremise16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((80 * (a 0 (axisSupportOfMask 0))) + (80 * (a 0 (axisSupportOfMask 1))) + ((-40) * (a 0 (axisSupportOfMask 2))) + ((-40) * (a 0 (axisSupportOfMask 3))) + ((-20) * (a 0 (axisSupportOfMask 4))) + ((-20) * (a 0 (axisSupportOfMask 5))) + (10 * (a 0 (axisSupportOfMask 6))) + (10 * (a 0 (axisSupportOfMask 7))) + (80 * (a 0 (axisSupportOfMask 8))) + (80 * (a 0 (axisSupportOfMask 9))) + ((-40) * (a 0 (axisSupportOfMask 10))) + ((-40) * (a 0 (axisSupportOfMask 11))) + ((-20) * (a 0 (axisSupportOfMask 12))) + ((-20) * (a 0 (axisSupportOfMask 13))) + (10 * (a 0 (axisSupportOfMask 14))) + (10 * (a 0 (axisSupportOfMask 15))) + ((-8) * (a 0 (axisSupportOfMask 16))) + ((-8) * (a 0 (axisSupportOfMask 17))) + (4 * (a 0 (axisSupportOfMask 18))) + (4 * (a 0 (axisSupportOfMask 19))) + (2 * (a 0 (axisSupportOfMask 20))) + (2 * (a 0 (axisSupportOfMask 21))) + ((-1) * (a 0 (axisSupportOfMask 22))) + ((-1) * (a 0 (axisSupportOfMask 23))) + ((-8) * (a 0 (axisSupportOfMask 24))) + ((-8) * (a 0 (axisSupportOfMask 25))) + (4 * (a 0 (axisSupportOfMask 26))) + (4 * (a 0 (axisSupportOfMask 27))) + (2 * (a 0 (axisSupportOfMask 28))) + (2 * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 22) (by decide)
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

/-- Core premise 17; source assertion 203. -/
theorem k242CorePremise17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((80 * (a 0 (axisSupportOfMask 0))) + ((-80) * (a 0 (axisSupportOfMask 1))) + ((-40) * (a 0 (axisSupportOfMask 2))) + (40 * (a 0 (axisSupportOfMask 3))) + ((-20) * (a 0 (axisSupportOfMask 4))) + (20 * (a 0 (axisSupportOfMask 5))) + (10 * (a 0 (axisSupportOfMask 6))) + ((-10) * (a 0 (axisSupportOfMask 7))) + (80 * (a 0 (axisSupportOfMask 8))) + ((-80) * (a 0 (axisSupportOfMask 9))) + ((-40) * (a 0 (axisSupportOfMask 10))) + (40 * (a 0 (axisSupportOfMask 11))) + ((-20) * (a 0 (axisSupportOfMask 12))) + (20 * (a 0 (axisSupportOfMask 13))) + (10 * (a 0 (axisSupportOfMask 14))) + ((-10) * (a 0 (axisSupportOfMask 15))) + ((-8) * (a 0 (axisSupportOfMask 16))) + (8 * (a 0 (axisSupportOfMask 17))) + (4 * (a 0 (axisSupportOfMask 18))) + ((-4) * (a 0 (axisSupportOfMask 19))) + (2 * (a 0 (axisSupportOfMask 20))) + ((-2) * (a 0 (axisSupportOfMask 21))) + ((-1) * (a 0 (axisSupportOfMask 22))) + (1 * (a 0 (axisSupportOfMask 23))) + ((-8) * (a 0 (axisSupportOfMask 24))) + (8 * (a 0 (axisSupportOfMask 25))) + (4 * (a 0 (axisSupportOfMask 26))) + ((-4) * (a 0 (axisSupportOfMask 27))) + (2 * (a 0 (axisSupportOfMask 28))) + ((-2) * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 23) (by decide)
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

/-- Core premise 18; source assertion 207. -/
theorem k242CorePremise18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((60 * (a 0 (axisSupportOfMask 0))) + ((-60) * (a 0 (axisSupportOfMask 1))) + (60 * (a 0 (axisSupportOfMask 2))) + ((-60) * (a 0 (axisSupportOfMask 3))) + (60 * (a 0 (axisSupportOfMask 4))) + ((-60) * (a 0 (axisSupportOfMask 5))) + (60 * (a 0 (axisSupportOfMask 6))) + ((-60) * (a 0 (axisSupportOfMask 7))) + ((-10) * (a 0 (axisSupportOfMask 8))) + (10 * (a 0 (axisSupportOfMask 9))) + ((-10) * (a 0 (axisSupportOfMask 10))) + (10 * (a 0 (axisSupportOfMask 11))) + ((-10) * (a 0 (axisSupportOfMask 12))) + (10 * (a 0 (axisSupportOfMask 13))) + ((-10) * (a 0 (axisSupportOfMask 14))) + (10 * (a 0 (axisSupportOfMask 15))) + ((-6) * (a 0 (axisSupportOfMask 16))) + (6 * (a 0 (axisSupportOfMask 17))) + ((-6) * (a 0 (axisSupportOfMask 18))) + (6 * (a 0 (axisSupportOfMask 19))) + ((-6) * (a 0 (axisSupportOfMask 20))) + (6 * (a 0 (axisSupportOfMask 21))) + ((-6) * (a 0 (axisSupportOfMask 22))) + (6 * (a 0 (axisSupportOfMask 23))) + (1 * (a 0 (axisSupportOfMask 24))) + ((-1) * (a 0 (axisSupportOfMask 25))) + (1 * (a 0 (axisSupportOfMask 26))) + ((-1) * (a 0 (axisSupportOfMask 27))) + (1 * (a 0 (axisSupportOfMask 28))) + ((-1) * (a 0 (axisSupportOfMask 29))) + (1 * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 25) (by decide)
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

/-- Core premise 19; source assertion 209. -/
theorem k242CorePremise19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((120 * (a 0 (axisSupportOfMask 0))) + (120 * (a 0 (axisSupportOfMask 1))) + ((-60) * (a 0 (axisSupportOfMask 2))) + ((-60) * (a 0 (axisSupportOfMask 3))) + (120 * (a 0 (axisSupportOfMask 4))) + (120 * (a 0 (axisSupportOfMask 5))) + ((-60) * (a 0 (axisSupportOfMask 6))) + ((-60) * (a 0 (axisSupportOfMask 7))) + ((-20) * (a 0 (axisSupportOfMask 8))) + ((-20) * (a 0 (axisSupportOfMask 9))) + (10 * (a 0 (axisSupportOfMask 10))) + (10 * (a 0 (axisSupportOfMask 11))) + ((-20) * (a 0 (axisSupportOfMask 12))) + ((-20) * (a 0 (axisSupportOfMask 13))) + (10 * (a 0 (axisSupportOfMask 14))) + (10 * (a 0 (axisSupportOfMask 15))) + ((-12) * (a 0 (axisSupportOfMask 16))) + ((-12) * (a 0 (axisSupportOfMask 17))) + (6 * (a 0 (axisSupportOfMask 18))) + (6 * (a 0 (axisSupportOfMask 19))) + ((-12) * (a 0 (axisSupportOfMask 20))) + ((-12) * (a 0 (axisSupportOfMask 21))) + (6 * (a 0 (axisSupportOfMask 22))) + (6 * (a 0 (axisSupportOfMask 23))) + (2 * (a 0 (axisSupportOfMask 24))) + (2 * (a 0 (axisSupportOfMask 25))) + ((-1) * (a 0 (axisSupportOfMask 26))) + ((-1) * (a 0 (axisSupportOfMask 27))) + (2 * (a 0 (axisSupportOfMask 28))) + (2 * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + ((-1) * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 26) (by decide)
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

end Fuglede
