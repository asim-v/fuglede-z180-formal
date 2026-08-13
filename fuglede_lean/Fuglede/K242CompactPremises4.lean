import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 4. -/

namespace Fuglede

/-- Core premise 40; source assertion 403. -/
theorem k242CorePremise40
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((2 * (a 1 (axisSupportOfMask 0))) + ((-2) * (a 1 (axisSupportOfMask 1))) + ((-1) * (a 1 (axisSupportOfMask 2))) + (1 * (a 1 (axisSupportOfMask 3))) + (2 * (a 1 (axisSupportOfMask 4))) + ((-2) * (a 1 (axisSupportOfMask 5))) + ((-1) * (a 1 (axisSupportOfMask 6))) + (1 * (a 1 (axisSupportOfMask 7))) + (2 * (a 1 (axisSupportOfMask 8))) + ((-2) * (a 1 (axisSupportOfMask 9))) + ((-1) * (a 1 (axisSupportOfMask 10))) + (1 * (a 1 (axisSupportOfMask 11))) + (2 * (a 1 (axisSupportOfMask 12))) + ((-2) * (a 1 (axisSupportOfMask 13))) + ((-1) * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (2 * (a 1 (axisSupportOfMask 16))) + ((-2) * (a 1 (axisSupportOfMask 17))) + ((-1) * (a 1 (axisSupportOfMask 18))) + (1 * (a 1 (axisSupportOfMask 19))) + (2 * (a 1 (axisSupportOfMask 20))) + ((-2) * (a 1 (axisSupportOfMask 21))) + ((-1) * (a 1 (axisSupportOfMask 22))) + (1 * (a 1 (axisSupportOfMask 23))) + (2 * (a 1 (axisSupportOfMask 24))) + ((-2) * (a 1 (axisSupportOfMask 25))) + ((-1) * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 3) (by decide)
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

/-- Core premise 41; source assertion 407. -/
theorem k242CorePremise41
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((4 * (a 1 (axisSupportOfMask 0))) + ((-4) * (a 1 (axisSupportOfMask 1))) + (4 * (a 1 (axisSupportOfMask 2))) + ((-4) * (a 1 (axisSupportOfMask 3))) + ((-1) * (a 1 (axisSupportOfMask 4))) + (1 * (a 1 (axisSupportOfMask 5))) + ((-1) * (a 1 (axisSupportOfMask 6))) + (1 * (a 1 (axisSupportOfMask 7))) + (4 * (a 1 (axisSupportOfMask 8))) + ((-4) * (a 1 (axisSupportOfMask 9))) + (4 * (a 1 (axisSupportOfMask 10))) + ((-4) * (a 1 (axisSupportOfMask 11))) + ((-1) * (a 1 (axisSupportOfMask 12))) + (1 * (a 1 (axisSupportOfMask 13))) + ((-1) * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (4 * (a 1 (axisSupportOfMask 16))) + ((-4) * (a 1 (axisSupportOfMask 17))) + (4 * (a 1 (axisSupportOfMask 18))) + ((-4) * (a 1 (axisSupportOfMask 19))) + ((-1) * (a 1 (axisSupportOfMask 20))) + (1 * (a 1 (axisSupportOfMask 21))) + ((-1) * (a 1 (axisSupportOfMask 22))) + (1 * (a 1 (axisSupportOfMask 23))) + (4 * (a 1 (axisSupportOfMask 24))) + ((-4) * (a 1 (axisSupportOfMask 25))) + (4 * (a 1 (axisSupportOfMask 26))) + ((-4) * (a 1 (axisSupportOfMask 27))) + ((-1) * (a 1 (axisSupportOfMask 28))) + (1 * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 5) (by decide)
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

/-- Core premise 42; source assertion 415. -/
theorem k242CorePremise42
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((6 * (a 1 (axisSupportOfMask 0))) + ((-6) * (a 1 (axisSupportOfMask 1))) + (6 * (a 1 (axisSupportOfMask 2))) + ((-6) * (a 1 (axisSupportOfMask 3))) + (6 * (a 1 (axisSupportOfMask 4))) + ((-6) * (a 1 (axisSupportOfMask 5))) + (6 * (a 1 (axisSupportOfMask 6))) + ((-6) * (a 1 (axisSupportOfMask 7))) + ((-1) * (a 1 (axisSupportOfMask 8))) + (1 * (a 1 (axisSupportOfMask 9))) + ((-1) * (a 1 (axisSupportOfMask 10))) + (1 * (a 1 (axisSupportOfMask 11))) + ((-1) * (a 1 (axisSupportOfMask 12))) + (1 * (a 1 (axisSupportOfMask 13))) + ((-1) * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (6 * (a 1 (axisSupportOfMask 16))) + ((-6) * (a 1 (axisSupportOfMask 17))) + (6 * (a 1 (axisSupportOfMask 18))) + ((-6) * (a 1 (axisSupportOfMask 19))) + (6 * (a 1 (axisSupportOfMask 20))) + ((-6) * (a 1 (axisSupportOfMask 21))) + (6 * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + ((-1) * (a 1 (axisSupportOfMask 24))) + (1 * (a 1 (axisSupportOfMask 25))) + ((-1) * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + ((-1) * (a 1 (axisSupportOfMask 28))) + (1 * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 9) (by decide)
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

/-- Core premise 43; source assertion 418. -/
theorem k242CorePremise43
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((z 1 (axisSupportOfMask 10)) ↔ (((12 * (a 1 (axisSupportOfMask 0))) + (12 * (a 1 (axisSupportOfMask 1))) + ((-6) * (a 1 (axisSupportOfMask 2))) + ((-6) * (a 1 (axisSupportOfMask 3))) + (12 * (a 1 (axisSupportOfMask 4))) + (12 * (a 1 (axisSupportOfMask 5))) + ((-6) * (a 1 (axisSupportOfMask 6))) + ((-6) * (a 1 (axisSupportOfMask 7))) + ((-2) * (a 1 (axisSupportOfMask 8))) + ((-2) * (a 1 (axisSupportOfMask 9))) + (1 * (a 1 (axisSupportOfMask 10))) + (1 * (a 1 (axisSupportOfMask 11))) + ((-2) * (a 1 (axisSupportOfMask 12))) + ((-2) * (a 1 (axisSupportOfMask 13))) + (1 * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (12 * (a 1 (axisSupportOfMask 16))) + (12 * (a 1 (axisSupportOfMask 17))) + ((-6) * (a 1 (axisSupportOfMask 18))) + ((-6) * (a 1 (axisSupportOfMask 19))) + (12 * (a 1 (axisSupportOfMask 20))) + (12 * (a 1 (axisSupportOfMask 21))) + ((-6) * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + ((-2) * (a 1 (axisSupportOfMask 24))) + ((-2) * (a 1 (axisSupportOfMask 25))) + (1 * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + ((-2) * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) = 0)) := by
  have hzero := hconstraints.zero_iff_energy 1 (axisSupportOfMask 10) (by decide)
  constructor
  · intro hz
    have henergy := hzero.mp hz
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
  · intro henergy
    apply hzero.mpr
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
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
      maskKrawtchoukCoeff_10_31] at ⊢
    norm_num at henergy ⊢
    linarith only [henergy]

/-- Core premise 44; source assertion 422. -/
theorem k242CorePremise44
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((z 1 (axisSupportOfMask 12)) ↔ (((24 * (a 1 (axisSupportOfMask 0))) + (24 * (a 1 (axisSupportOfMask 1))) + (24 * (a 1 (axisSupportOfMask 2))) + (24 * (a 1 (axisSupportOfMask 3))) + ((-6) * (a 1 (axisSupportOfMask 4))) + ((-6) * (a 1 (axisSupportOfMask 5))) + ((-6) * (a 1 (axisSupportOfMask 6))) + ((-6) * (a 1 (axisSupportOfMask 7))) + ((-4) * (a 1 (axisSupportOfMask 8))) + ((-4) * (a 1 (axisSupportOfMask 9))) + ((-4) * (a 1 (axisSupportOfMask 10))) + ((-4) * (a 1 (axisSupportOfMask 11))) + (1 * (a 1 (axisSupportOfMask 12))) + (1 * (a 1 (axisSupportOfMask 13))) + (1 * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (24 * (a 1 (axisSupportOfMask 16))) + (24 * (a 1 (axisSupportOfMask 17))) + (24 * (a 1 (axisSupportOfMask 18))) + (24 * (a 1 (axisSupportOfMask 19))) + ((-6) * (a 1 (axisSupportOfMask 20))) + ((-6) * (a 1 (axisSupportOfMask 21))) + ((-6) * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + ((-4) * (a 1 (axisSupportOfMask 24))) + ((-4) * (a 1 (axisSupportOfMask 25))) + ((-4) * (a 1 (axisSupportOfMask 26))) + ((-4) * (a 1 (axisSupportOfMask 27))) + (1 * (a 1 (axisSupportOfMask 28))) + (1 * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) = 0)) := by
  have hzero := hconstraints.zero_iff_energy 1 (axisSupportOfMask 12) (by decide)
  constructor
  · intro hz
    have henergy := hzero.mp hz
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_12_0,
      maskKrawtchoukCoeff_12_1,
      maskKrawtchoukCoeff_12_2,
      maskKrawtchoukCoeff_12_3,
      maskKrawtchoukCoeff_12_4,
      maskKrawtchoukCoeff_12_5,
      maskKrawtchoukCoeff_12_6,
      maskKrawtchoukCoeff_12_7,
      maskKrawtchoukCoeff_12_8,
      maskKrawtchoukCoeff_12_9,
      maskKrawtchoukCoeff_12_10,
      maskKrawtchoukCoeff_12_11,
      maskKrawtchoukCoeff_12_12,
      maskKrawtchoukCoeff_12_13,
      maskKrawtchoukCoeff_12_14,
      maskKrawtchoukCoeff_12_15,
      maskKrawtchoukCoeff_12_16,
      maskKrawtchoukCoeff_12_17,
      maskKrawtchoukCoeff_12_18,
      maskKrawtchoukCoeff_12_19,
      maskKrawtchoukCoeff_12_20,
      maskKrawtchoukCoeff_12_21,
      maskKrawtchoukCoeff_12_22,
      maskKrawtchoukCoeff_12_23,
      maskKrawtchoukCoeff_12_24,
      maskKrawtchoukCoeff_12_25,
      maskKrawtchoukCoeff_12_26,
      maskKrawtchoukCoeff_12_27,
      maskKrawtchoukCoeff_12_28,
      maskKrawtchoukCoeff_12_29,
      maskKrawtchoukCoeff_12_30,
      maskKrawtchoukCoeff_12_31] at henergy
    norm_num at henergy ⊢
    linarith only [henergy]
  · intro henergy
    apply hzero.mpr
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_12_0,
      maskKrawtchoukCoeff_12_1,
      maskKrawtchoukCoeff_12_2,
      maskKrawtchoukCoeff_12_3,
      maskKrawtchoukCoeff_12_4,
      maskKrawtchoukCoeff_12_5,
      maskKrawtchoukCoeff_12_6,
      maskKrawtchoukCoeff_12_7,
      maskKrawtchoukCoeff_12_8,
      maskKrawtchoukCoeff_12_9,
      maskKrawtchoukCoeff_12_10,
      maskKrawtchoukCoeff_12_11,
      maskKrawtchoukCoeff_12_12,
      maskKrawtchoukCoeff_12_13,
      maskKrawtchoukCoeff_12_14,
      maskKrawtchoukCoeff_12_15,
      maskKrawtchoukCoeff_12_16,
      maskKrawtchoukCoeff_12_17,
      maskKrawtchoukCoeff_12_18,
      maskKrawtchoukCoeff_12_19,
      maskKrawtchoukCoeff_12_20,
      maskKrawtchoukCoeff_12_21,
      maskKrawtchoukCoeff_12_22,
      maskKrawtchoukCoeff_12_23,
      maskKrawtchoukCoeff_12_24,
      maskKrawtchoukCoeff_12_25,
      maskKrawtchoukCoeff_12_26,
      maskKrawtchoukCoeff_12_27,
      maskKrawtchoukCoeff_12_28,
      maskKrawtchoukCoeff_12_29,
      maskKrawtchoukCoeff_12_30,
      maskKrawtchoukCoeff_12_31] at ⊢
    norm_num at henergy ⊢
    linarith only [henergy]

/-- Core premise 45; source assertion 426. -/
theorem k242CorePremise45
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((z 1 (axisSupportOfMask 14)) ↔ (((48 * (a 1 (axisSupportOfMask 0))) + (48 * (a 1 (axisSupportOfMask 1))) + ((-24) * (a 1 (axisSupportOfMask 2))) + ((-24) * (a 1 (axisSupportOfMask 3))) + ((-12) * (a 1 (axisSupportOfMask 4))) + ((-12) * (a 1 (axisSupportOfMask 5))) + (6 * (a 1 (axisSupportOfMask 6))) + (6 * (a 1 (axisSupportOfMask 7))) + ((-8) * (a 1 (axisSupportOfMask 8))) + ((-8) * (a 1 (axisSupportOfMask 9))) + (4 * (a 1 (axisSupportOfMask 10))) + (4 * (a 1 (axisSupportOfMask 11))) + (2 * (a 1 (axisSupportOfMask 12))) + (2 * (a 1 (axisSupportOfMask 13))) + ((-1) * (a 1 (axisSupportOfMask 14))) + ((-1) * (a 1 (axisSupportOfMask 15))) + (48 * (a 1 (axisSupportOfMask 16))) + (48 * (a 1 (axisSupportOfMask 17))) + ((-24) * (a 1 (axisSupportOfMask 18))) + ((-24) * (a 1 (axisSupportOfMask 19))) + ((-12) * (a 1 (axisSupportOfMask 20))) + ((-12) * (a 1 (axisSupportOfMask 21))) + (6 * (a 1 (axisSupportOfMask 22))) + (6 * (a 1 (axisSupportOfMask 23))) + ((-8) * (a 1 (axisSupportOfMask 24))) + ((-8) * (a 1 (axisSupportOfMask 25))) + (4 * (a 1 (axisSupportOfMask 26))) + (4 * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + (2 * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) = 0)) := by
  have hzero := hconstraints.zero_iff_energy 1 (axisSupportOfMask 14) (by decide)
  constructor
  · intro hz
    have henergy := hzero.mp hz
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_14_0,
      maskKrawtchoukCoeff_14_1,
      maskKrawtchoukCoeff_14_2,
      maskKrawtchoukCoeff_14_3,
      maskKrawtchoukCoeff_14_4,
      maskKrawtchoukCoeff_14_5,
      maskKrawtchoukCoeff_14_6,
      maskKrawtchoukCoeff_14_7,
      maskKrawtchoukCoeff_14_8,
      maskKrawtchoukCoeff_14_9,
      maskKrawtchoukCoeff_14_10,
      maskKrawtchoukCoeff_14_11,
      maskKrawtchoukCoeff_14_12,
      maskKrawtchoukCoeff_14_13,
      maskKrawtchoukCoeff_14_14,
      maskKrawtchoukCoeff_14_15,
      maskKrawtchoukCoeff_14_16,
      maskKrawtchoukCoeff_14_17,
      maskKrawtchoukCoeff_14_18,
      maskKrawtchoukCoeff_14_19,
      maskKrawtchoukCoeff_14_20,
      maskKrawtchoukCoeff_14_21,
      maskKrawtchoukCoeff_14_22,
      maskKrawtchoukCoeff_14_23,
      maskKrawtchoukCoeff_14_24,
      maskKrawtchoukCoeff_14_25,
      maskKrawtchoukCoeff_14_26,
      maskKrawtchoukCoeff_14_27,
      maskKrawtchoukCoeff_14_28,
      maskKrawtchoukCoeff_14_29,
      maskKrawtchoukCoeff_14_30,
      maskKrawtchoukCoeff_14_31] at henergy
    norm_num at henergy ⊢
    linarith only [henergy]
  · intro henergy
    apply hzero.mpr
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_14_0,
      maskKrawtchoukCoeff_14_1,
      maskKrawtchoukCoeff_14_2,
      maskKrawtchoukCoeff_14_3,
      maskKrawtchoukCoeff_14_4,
      maskKrawtchoukCoeff_14_5,
      maskKrawtchoukCoeff_14_6,
      maskKrawtchoukCoeff_14_7,
      maskKrawtchoukCoeff_14_8,
      maskKrawtchoukCoeff_14_9,
      maskKrawtchoukCoeff_14_10,
      maskKrawtchoukCoeff_14_11,
      maskKrawtchoukCoeff_14_12,
      maskKrawtchoukCoeff_14_13,
      maskKrawtchoukCoeff_14_14,
      maskKrawtchoukCoeff_14_15,
      maskKrawtchoukCoeff_14_16,
      maskKrawtchoukCoeff_14_17,
      maskKrawtchoukCoeff_14_18,
      maskKrawtchoukCoeff_14_19,
      maskKrawtchoukCoeff_14_20,
      maskKrawtchoukCoeff_14_21,
      maskKrawtchoukCoeff_14_22,
      maskKrawtchoukCoeff_14_23,
      maskKrawtchoukCoeff_14_24,
      maskKrawtchoukCoeff_14_25,
      maskKrawtchoukCoeff_14_26,
      maskKrawtchoukCoeff_14_27,
      maskKrawtchoukCoeff_14_28,
      maskKrawtchoukCoeff_14_29,
      maskKrawtchoukCoeff_14_30,
      maskKrawtchoukCoeff_14_31] at ⊢
    norm_num at henergy ⊢
    linarith only [henergy]

/-- Core premise 46; source assertion 428. -/
theorem k242CorePremise46
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((z 1 (axisSupportOfMask 15)) ↔ (((48 * (a 1 (axisSupportOfMask 0))) + ((-48) * (a 1 (axisSupportOfMask 1))) + ((-24) * (a 1 (axisSupportOfMask 2))) + (24 * (a 1 (axisSupportOfMask 3))) + ((-12) * (a 1 (axisSupportOfMask 4))) + (12 * (a 1 (axisSupportOfMask 5))) + (6 * (a 1 (axisSupportOfMask 6))) + ((-6) * (a 1 (axisSupportOfMask 7))) + ((-8) * (a 1 (axisSupportOfMask 8))) + (8 * (a 1 (axisSupportOfMask 9))) + (4 * (a 1 (axisSupportOfMask 10))) + ((-4) * (a 1 (axisSupportOfMask 11))) + (2 * (a 1 (axisSupportOfMask 12))) + ((-2) * (a 1 (axisSupportOfMask 13))) + ((-1) * (a 1 (axisSupportOfMask 14))) + (1 * (a 1 (axisSupportOfMask 15))) + (48 * (a 1 (axisSupportOfMask 16))) + ((-48) * (a 1 (axisSupportOfMask 17))) + ((-24) * (a 1 (axisSupportOfMask 18))) + (24 * (a 1 (axisSupportOfMask 19))) + ((-12) * (a 1 (axisSupportOfMask 20))) + (12 * (a 1 (axisSupportOfMask 21))) + (6 * (a 1 (axisSupportOfMask 22))) + ((-6) * (a 1 (axisSupportOfMask 23))) + ((-8) * (a 1 (axisSupportOfMask 24))) + (8 * (a 1 (axisSupportOfMask 25))) + (4 * (a 1 (axisSupportOfMask 26))) + ((-4) * (a 1 (axisSupportOfMask 27))) + (2 * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) = 0)) := by
  have hzero := hconstraints.zero_iff_energy 1 (axisSupportOfMask 15) (by decide)
  constructor
  · intro hz
    have henergy := hzero.mp hz
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_15_0,
      maskKrawtchoukCoeff_15_1,
      maskKrawtchoukCoeff_15_2,
      maskKrawtchoukCoeff_15_3,
      maskKrawtchoukCoeff_15_4,
      maskKrawtchoukCoeff_15_5,
      maskKrawtchoukCoeff_15_6,
      maskKrawtchoukCoeff_15_7,
      maskKrawtchoukCoeff_15_8,
      maskKrawtchoukCoeff_15_9,
      maskKrawtchoukCoeff_15_10,
      maskKrawtchoukCoeff_15_11,
      maskKrawtchoukCoeff_15_12,
      maskKrawtchoukCoeff_15_13,
      maskKrawtchoukCoeff_15_14,
      maskKrawtchoukCoeff_15_15,
      maskKrawtchoukCoeff_15_16,
      maskKrawtchoukCoeff_15_17,
      maskKrawtchoukCoeff_15_18,
      maskKrawtchoukCoeff_15_19,
      maskKrawtchoukCoeff_15_20,
      maskKrawtchoukCoeff_15_21,
      maskKrawtchoukCoeff_15_22,
      maskKrawtchoukCoeff_15_23,
      maskKrawtchoukCoeff_15_24,
      maskKrawtchoukCoeff_15_25,
      maskKrawtchoukCoeff_15_26,
      maskKrawtchoukCoeff_15_27,
      maskKrawtchoukCoeff_15_28,
      maskKrawtchoukCoeff_15_29,
      maskKrawtchoukCoeff_15_30,
      maskKrawtchoukCoeff_15_31] at henergy
    norm_num at henergy ⊢
    linarith only [henergy]
  · intro henergy
    apply hzero.mpr
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_15_0,
      maskKrawtchoukCoeff_15_1,
      maskKrawtchoukCoeff_15_2,
      maskKrawtchoukCoeff_15_3,
      maskKrawtchoukCoeff_15_4,
      maskKrawtchoukCoeff_15_5,
      maskKrawtchoukCoeff_15_6,
      maskKrawtchoukCoeff_15_7,
      maskKrawtchoukCoeff_15_8,
      maskKrawtchoukCoeff_15_9,
      maskKrawtchoukCoeff_15_10,
      maskKrawtchoukCoeff_15_11,
      maskKrawtchoukCoeff_15_12,
      maskKrawtchoukCoeff_15_13,
      maskKrawtchoukCoeff_15_14,
      maskKrawtchoukCoeff_15_15,
      maskKrawtchoukCoeff_15_16,
      maskKrawtchoukCoeff_15_17,
      maskKrawtchoukCoeff_15_18,
      maskKrawtchoukCoeff_15_19,
      maskKrawtchoukCoeff_15_20,
      maskKrawtchoukCoeff_15_21,
      maskKrawtchoukCoeff_15_22,
      maskKrawtchoukCoeff_15_23,
      maskKrawtchoukCoeff_15_24,
      maskKrawtchoukCoeff_15_25,
      maskKrawtchoukCoeff_15_26,
      maskKrawtchoukCoeff_15_27,
      maskKrawtchoukCoeff_15_28,
      maskKrawtchoukCoeff_15_29,
      maskKrawtchoukCoeff_15_30,
      maskKrawtchoukCoeff_15_31] at ⊢
    norm_num at henergy ⊢
    linarith only [henergy]

/-- Core premise 47; source assertion 430. -/
theorem k242CorePremise47
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((z 1 (axisSupportOfMask 16)) ↔ (((10 * (a 1 (axisSupportOfMask 0))) + (10 * (a 1 (axisSupportOfMask 1))) + (10 * (a 1 (axisSupportOfMask 2))) + (10 * (a 1 (axisSupportOfMask 3))) + (10 * (a 1 (axisSupportOfMask 4))) + (10 * (a 1 (axisSupportOfMask 5))) + (10 * (a 1 (axisSupportOfMask 6))) + (10 * (a 1 (axisSupportOfMask 7))) + (10 * (a 1 (axisSupportOfMask 8))) + (10 * (a 1 (axisSupportOfMask 9))) + (10 * (a 1 (axisSupportOfMask 10))) + (10 * (a 1 (axisSupportOfMask 11))) + (10 * (a 1 (axisSupportOfMask 12))) + (10 * (a 1 (axisSupportOfMask 13))) + (10 * (a 1 (axisSupportOfMask 14))) + (10 * (a 1 (axisSupportOfMask 15))) + ((-1) * (a 1 (axisSupportOfMask 16))) + ((-1) * (a 1 (axisSupportOfMask 17))) + ((-1) * (a 1 (axisSupportOfMask 18))) + ((-1) * (a 1 (axisSupportOfMask 19))) + ((-1) * (a 1 (axisSupportOfMask 20))) + ((-1) * (a 1 (axisSupportOfMask 21))) + ((-1) * (a 1 (axisSupportOfMask 22))) + ((-1) * (a 1 (axisSupportOfMask 23))) + ((-1) * (a 1 (axisSupportOfMask 24))) + ((-1) * (a 1 (axisSupportOfMask 25))) + ((-1) * (a 1 (axisSupportOfMask 26))) + ((-1) * (a 1 (axisSupportOfMask 27))) + ((-1) * (a 1 (axisSupportOfMask 28))) + ((-1) * (a 1 (axisSupportOfMask 29))) + ((-1) * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) = 0)) := by
  have hzero := hconstraints.zero_iff_energy 1 (axisSupportOfMask 16) (by decide)
  constructor
  · intro hz
    have henergy := hzero.mp hz
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_16_0,
      maskKrawtchoukCoeff_16_1,
      maskKrawtchoukCoeff_16_2,
      maskKrawtchoukCoeff_16_3,
      maskKrawtchoukCoeff_16_4,
      maskKrawtchoukCoeff_16_5,
      maskKrawtchoukCoeff_16_6,
      maskKrawtchoukCoeff_16_7,
      maskKrawtchoukCoeff_16_8,
      maskKrawtchoukCoeff_16_9,
      maskKrawtchoukCoeff_16_10,
      maskKrawtchoukCoeff_16_11,
      maskKrawtchoukCoeff_16_12,
      maskKrawtchoukCoeff_16_13,
      maskKrawtchoukCoeff_16_14,
      maskKrawtchoukCoeff_16_15,
      maskKrawtchoukCoeff_16_16,
      maskKrawtchoukCoeff_16_17,
      maskKrawtchoukCoeff_16_18,
      maskKrawtchoukCoeff_16_19,
      maskKrawtchoukCoeff_16_20,
      maskKrawtchoukCoeff_16_21,
      maskKrawtchoukCoeff_16_22,
      maskKrawtchoukCoeff_16_23,
      maskKrawtchoukCoeff_16_24,
      maskKrawtchoukCoeff_16_25,
      maskKrawtchoukCoeff_16_26,
      maskKrawtchoukCoeff_16_27,
      maskKrawtchoukCoeff_16_28,
      maskKrawtchoukCoeff_16_29,
      maskKrawtchoukCoeff_16_30,
      maskKrawtchoukCoeff_16_31] at henergy
    norm_num at henergy ⊢
    linarith only [henergy]
  · intro henergy
    apply hzero.mpr
    rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
    simp only [
      krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_16_0,
      maskKrawtchoukCoeff_16_1,
      maskKrawtchoukCoeff_16_2,
      maskKrawtchoukCoeff_16_3,
      maskKrawtchoukCoeff_16_4,
      maskKrawtchoukCoeff_16_5,
      maskKrawtchoukCoeff_16_6,
      maskKrawtchoukCoeff_16_7,
      maskKrawtchoukCoeff_16_8,
      maskKrawtchoukCoeff_16_9,
      maskKrawtchoukCoeff_16_10,
      maskKrawtchoukCoeff_16_11,
      maskKrawtchoukCoeff_16_12,
      maskKrawtchoukCoeff_16_13,
      maskKrawtchoukCoeff_16_14,
      maskKrawtchoukCoeff_16_15,
      maskKrawtchoukCoeff_16_16,
      maskKrawtchoukCoeff_16_17,
      maskKrawtchoukCoeff_16_18,
      maskKrawtchoukCoeff_16_19,
      maskKrawtchoukCoeff_16_20,
      maskKrawtchoukCoeff_16_21,
      maskKrawtchoukCoeff_16_22,
      maskKrawtchoukCoeff_16_23,
      maskKrawtchoukCoeff_16_24,
      maskKrawtchoukCoeff_16_25,
      maskKrawtchoukCoeff_16_26,
      maskKrawtchoukCoeff_16_27,
      maskKrawtchoukCoeff_16_28,
      maskKrawtchoukCoeff_16_29,
      maskKrawtchoukCoeff_16_30,
      maskKrawtchoukCoeff_16_31] at ⊢
    norm_num at henergy ⊢
    linarith only [henergy]

/-- Core premise 48; source assertion 433. -/
theorem k242CorePremise48
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((20 * (a 1 (axisSupportOfMask 0))) + (20 * (a 1 (axisSupportOfMask 1))) + ((-10) * (a 1 (axisSupportOfMask 2))) + ((-10) * (a 1 (axisSupportOfMask 3))) + (20 * (a 1 (axisSupportOfMask 4))) + (20 * (a 1 (axisSupportOfMask 5))) + ((-10) * (a 1 (axisSupportOfMask 6))) + ((-10) * (a 1 (axisSupportOfMask 7))) + (20 * (a 1 (axisSupportOfMask 8))) + (20 * (a 1 (axisSupportOfMask 9))) + ((-10) * (a 1 (axisSupportOfMask 10))) + ((-10) * (a 1 (axisSupportOfMask 11))) + (20 * (a 1 (axisSupportOfMask 12))) + (20 * (a 1 (axisSupportOfMask 13))) + ((-10) * (a 1 (axisSupportOfMask 14))) + ((-10) * (a 1 (axisSupportOfMask 15))) + ((-2) * (a 1 (axisSupportOfMask 16))) + ((-2) * (a 1 (axisSupportOfMask 17))) + (1 * (a 1 (axisSupportOfMask 18))) + (1 * (a 1 (axisSupportOfMask 19))) + ((-2) * (a 1 (axisSupportOfMask 20))) + ((-2) * (a 1 (axisSupportOfMask 21))) + (1 * (a 1 (axisSupportOfMask 22))) + (1 * (a 1 (axisSupportOfMask 23))) + ((-2) * (a 1 (axisSupportOfMask 24))) + ((-2) * (a 1 (axisSupportOfMask 25))) + (1 * (a 1 (axisSupportOfMask 26))) + (1 * (a 1 (axisSupportOfMask 27))) + ((-2) * (a 1 (axisSupportOfMask 28))) + ((-2) * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + (1 * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 18) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_18_0,
    maskKrawtchoukCoeff_18_1,
    maskKrawtchoukCoeff_18_2,
    maskKrawtchoukCoeff_18_3,
    maskKrawtchoukCoeff_18_4,
    maskKrawtchoukCoeff_18_5,
    maskKrawtchoukCoeff_18_6,
    maskKrawtchoukCoeff_18_7,
    maskKrawtchoukCoeff_18_8,
    maskKrawtchoukCoeff_18_9,
    maskKrawtchoukCoeff_18_10,
    maskKrawtchoukCoeff_18_11,
    maskKrawtchoukCoeff_18_12,
    maskKrawtchoukCoeff_18_13,
    maskKrawtchoukCoeff_18_14,
    maskKrawtchoukCoeff_18_15,
    maskKrawtchoukCoeff_18_16,
    maskKrawtchoukCoeff_18_17,
    maskKrawtchoukCoeff_18_18,
    maskKrawtchoukCoeff_18_19,
    maskKrawtchoukCoeff_18_20,
    maskKrawtchoukCoeff_18_21,
    maskKrawtchoukCoeff_18_22,
    maskKrawtchoukCoeff_18_23,
    maskKrawtchoukCoeff_18_24,
    maskKrawtchoukCoeff_18_25,
    maskKrawtchoukCoeff_18_26,
    maskKrawtchoukCoeff_18_27,
    maskKrawtchoukCoeff_18_28,
    maskKrawtchoukCoeff_18_29,
    maskKrawtchoukCoeff_18_30,
    maskKrawtchoukCoeff_18_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 49; source assertion 435. -/
theorem k242CorePremise49
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((20 * (a 1 (axisSupportOfMask 0))) + ((-20) * (a 1 (axisSupportOfMask 1))) + ((-10) * (a 1 (axisSupportOfMask 2))) + (10 * (a 1 (axisSupportOfMask 3))) + (20 * (a 1 (axisSupportOfMask 4))) + ((-20) * (a 1 (axisSupportOfMask 5))) + ((-10) * (a 1 (axisSupportOfMask 6))) + (10 * (a 1 (axisSupportOfMask 7))) + (20 * (a 1 (axisSupportOfMask 8))) + ((-20) * (a 1 (axisSupportOfMask 9))) + ((-10) * (a 1 (axisSupportOfMask 10))) + (10 * (a 1 (axisSupportOfMask 11))) + (20 * (a 1 (axisSupportOfMask 12))) + ((-20) * (a 1 (axisSupportOfMask 13))) + ((-10) * (a 1 (axisSupportOfMask 14))) + (10 * (a 1 (axisSupportOfMask 15))) + ((-2) * (a 1 (axisSupportOfMask 16))) + (2 * (a 1 (axisSupportOfMask 17))) + (1 * (a 1 (axisSupportOfMask 18))) + ((-1) * (a 1 (axisSupportOfMask 19))) + ((-2) * (a 1 (axisSupportOfMask 20))) + (2 * (a 1 (axisSupportOfMask 21))) + (1 * (a 1 (axisSupportOfMask 22))) + ((-1) * (a 1 (axisSupportOfMask 23))) + ((-2) * (a 1 (axisSupportOfMask 24))) + (2 * (a 1 (axisSupportOfMask 25))) + (1 * (a 1 (axisSupportOfMask 26))) + ((-1) * (a 1 (axisSupportOfMask 27))) + ((-2) * (a 1 (axisSupportOfMask 28))) + (2 * (a 1 (axisSupportOfMask 29))) + (1 * (a 1 (axisSupportOfMask 30))) + ((-1) * (a 1 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 1 (axisSupportOfMask 19) (by decide)
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

end Fuglede
