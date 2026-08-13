import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # Compact multiaxis normalization

This generated module is independent of the cardinality and the selected SMT
core.  It packages the two `Fin 2 → Fin 32` families used by compact raw
certificates and pre-normalizes every energy and projection row exactly once.
-/

namespace Fuglede

/-- Restrict a typed inner-distribution family to the 32 mask coordinates. -/
def aMask
    (a : SpectralPairSide → AxisSupport2310 → Int) :
    Fin 2 → Fin 32 → Int :=
  fun side mask => a side (axisSupportOfMask mask.val)

/-- Restrict a typed energy-zero family to the 32 mask coordinates. -/
def zMask
    (z : SpectralPairSide → AxisSupport2310 → Prop) :
    Fin 2 → Fin 32 → Prop :=
  fun side mask => z side (axisSupportOfMask mask.val)

@[simp] theorem aMask_apply
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : Fin 2) (mask : Fin 32) :
    aMask a side mask = a side (axisSupportOfMask mask.val) := rfl

@[simp] theorem zMask_apply
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (side : Fin 2) (mask : Fin 32) :
    zMask z side mask ↔ z side (axisSupportOfMask mask.val) := Iff.rfl

/-- The mask-indexed form of one Krawtchouk energy row. -/
def compactMultiaxisEnergy
    (a : Fin 2 → Fin 32 → Int) (side : Fin 2) (row : Fin 32) : Int :=
  ∑ column : Fin 32,
    maskKrawtchoukCoeff row.val column.val * a side column

/-- The mask-indexed form of one projection-collision row. -/
def compactMultiaxisProjectionCollision
    (a : Fin 2 → Fin 32 → Int) (side : Fin 2) (mask : Fin 32) : Int :=
  ∑ column : Fin 32,
    if Disjoint (axisSupportOfMask column.val) (axisSupportOfMask mask.val) then
      a side column
    else 0

/-- Generic total-mass normalization through `aMask`. -/
theorem multiaxisMass_eq_compact
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    (∑ D : AxisSupport2310, a side D) =
      ∑ mask : Fin 32, aMask a side mask := by
  simpa [aMask] using sum_axisSupportOfMask (fun D => a side D)

/-- Generic energy normalization through `aMask`. -/
theorem multiaxisEnergy_eq_compact
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (row : Fin 32) :
    multiaxisEnergy a side (axisSupportOfMask row.val) =
      compactMultiaxisEnergy (aMask a) side row := by
  rw [multiaxisEnergy, sum_axisSupportOfMask]
  simp only [aMask, compactMultiaxisEnergy,
    krawtchoukCoeff_axisSupportOfMask]

/-- Generic projection-collision normalization through `aMask`. -/
theorem multiaxisProjectionCollision_eq_compact
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (mask : Fin 32) :
    multiaxisProjectionCollision a side (axisSupportOfMask mask.val) =
      compactMultiaxisProjectionCollision (aMask a) side mask := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask]
  rfl

/-- The total mass as the explicit 32-coordinate expression expected by raw
certificate hypotheses. -/
theorem multiaxisMass_aMask_explicit
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    (∑ D : AxisSupport2310, a side D) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 6 +
      aMask a side 7 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 10 +
      aMask a side 11 +
      aMask a side 12 +
      aMask a side 13 +
      aMask a side 14 +
      aMask a side 15 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 18 +
      aMask a side 19 +
      aMask a side 20 +
      aMask a side 21 +
      aMask a side 22 +
      aMask a side 23 +
      aMask a side 24 +
      aMask a side 25 +
      aMask a side 26 +
      aMask a side 27 +
      aMask a side 28 +
      aMask a side 29 +
      aMask a side 30 +
      aMask a side 31 := by
  rw [multiaxisMass_eq_compact]
  norm_num [Fin.sum_univ_succ] <;> ring

/-- Fully evaluated Krawtchouk row 0. -/
theorem multiaxisEnergy_aMask_row_0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 0) =
      (1 * aMask a side 0) +
      (1 * aMask a side 1) +
      (1 * aMask a side 2) +
      (1 * aMask a side 3) +
      (1 * aMask a side 4) +
      (1 * aMask a side 5) +
      (1 * aMask a side 6) +
      (1 * aMask a side 7) +
      (1 * aMask a side 8) +
      (1 * aMask a side 9) +
      (1 * aMask a side 10) +
      (1 * aMask a side 11) +
      (1 * aMask a side 12) +
      (1 * aMask a side 13) +
      (1 * aMask a side 14) +
      (1 * aMask a side 15) +
      (1 * aMask a side 16) +
      (1 * aMask a side 17) +
      (1 * aMask a side 18) +
      (1 * aMask a side 19) +
      (1 * aMask a side 20) +
      (1 * aMask a side 21) +
      (1 * aMask a side 22) +
      (1 * aMask a side 23) +
      (1 * aMask a side 24) +
      (1 * aMask a side 25) +
      (1 * aMask a side 26) +
      (1 * aMask a side 27) +
      (1 * aMask a side 28) +
      (1 * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_0_0,
      maskKrawtchoukCoeff_0_1,
      maskKrawtchoukCoeff_0_2,
      maskKrawtchoukCoeff_0_3,
      maskKrawtchoukCoeff_0_4,
      maskKrawtchoukCoeff_0_5,
      maskKrawtchoukCoeff_0_6,
      maskKrawtchoukCoeff_0_7,
      maskKrawtchoukCoeff_0_8,
      maskKrawtchoukCoeff_0_9,
      maskKrawtchoukCoeff_0_10,
      maskKrawtchoukCoeff_0_11,
      maskKrawtchoukCoeff_0_12,
      maskKrawtchoukCoeff_0_13,
      maskKrawtchoukCoeff_0_14,
      maskKrawtchoukCoeff_0_15,
      maskKrawtchoukCoeff_0_16,
      maskKrawtchoukCoeff_0_17,
      maskKrawtchoukCoeff_0_18,
      maskKrawtchoukCoeff_0_19,
      maskKrawtchoukCoeff_0_20,
      maskKrawtchoukCoeff_0_21,
      maskKrawtchoukCoeff_0_22,
      maskKrawtchoukCoeff_0_23,
      maskKrawtchoukCoeff_0_24,
      maskKrawtchoukCoeff_0_25,
      maskKrawtchoukCoeff_0_26,
      maskKrawtchoukCoeff_0_27,
      maskKrawtchoukCoeff_0_28,
      maskKrawtchoukCoeff_0_29,
      maskKrawtchoukCoeff_0_30,
      maskKrawtchoukCoeff_0_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 1. -/
theorem multiaxisEnergy_aMask_row_1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 1) =
      (1 * aMask a side 0) +
      ((-1) * aMask a side 1) +
      (1 * aMask a side 2) +
      ((-1) * aMask a side 3) +
      (1 * aMask a side 4) +
      ((-1) * aMask a side 5) +
      (1 * aMask a side 6) +
      ((-1) * aMask a side 7) +
      (1 * aMask a side 8) +
      ((-1) * aMask a side 9) +
      (1 * aMask a side 10) +
      ((-1) * aMask a side 11) +
      (1 * aMask a side 12) +
      ((-1) * aMask a side 13) +
      (1 * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (1 * aMask a side 16) +
      ((-1) * aMask a side 17) +
      (1 * aMask a side 18) +
      ((-1) * aMask a side 19) +
      (1 * aMask a side 20) +
      ((-1) * aMask a side 21) +
      (1 * aMask a side 22) +
      ((-1) * aMask a side 23) +
      (1 * aMask a side 24) +
      ((-1) * aMask a side 25) +
      (1 * aMask a side 26) +
      ((-1) * aMask a side 27) +
      (1 * aMask a side 28) +
      ((-1) * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_1_0,
      maskKrawtchoukCoeff_1_1,
      maskKrawtchoukCoeff_1_2,
      maskKrawtchoukCoeff_1_3,
      maskKrawtchoukCoeff_1_4,
      maskKrawtchoukCoeff_1_5,
      maskKrawtchoukCoeff_1_6,
      maskKrawtchoukCoeff_1_7,
      maskKrawtchoukCoeff_1_8,
      maskKrawtchoukCoeff_1_9,
      maskKrawtchoukCoeff_1_10,
      maskKrawtchoukCoeff_1_11,
      maskKrawtchoukCoeff_1_12,
      maskKrawtchoukCoeff_1_13,
      maskKrawtchoukCoeff_1_14,
      maskKrawtchoukCoeff_1_15,
      maskKrawtchoukCoeff_1_16,
      maskKrawtchoukCoeff_1_17,
      maskKrawtchoukCoeff_1_18,
      maskKrawtchoukCoeff_1_19,
      maskKrawtchoukCoeff_1_20,
      maskKrawtchoukCoeff_1_21,
      maskKrawtchoukCoeff_1_22,
      maskKrawtchoukCoeff_1_23,
      maskKrawtchoukCoeff_1_24,
      maskKrawtchoukCoeff_1_25,
      maskKrawtchoukCoeff_1_26,
      maskKrawtchoukCoeff_1_27,
      maskKrawtchoukCoeff_1_28,
      maskKrawtchoukCoeff_1_29,
      maskKrawtchoukCoeff_1_30,
      maskKrawtchoukCoeff_1_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 2. -/
theorem multiaxisEnergy_aMask_row_2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 2) =
      (2 * aMask a side 0) +
      (2 * aMask a side 1) +
      ((-1) * aMask a side 2) +
      ((-1) * aMask a side 3) +
      (2 * aMask a side 4) +
      (2 * aMask a side 5) +
      ((-1) * aMask a side 6) +
      ((-1) * aMask a side 7) +
      (2 * aMask a side 8) +
      (2 * aMask a side 9) +
      ((-1) * aMask a side 10) +
      ((-1) * aMask a side 11) +
      (2 * aMask a side 12) +
      (2 * aMask a side 13) +
      ((-1) * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (2 * aMask a side 16) +
      (2 * aMask a side 17) +
      ((-1) * aMask a side 18) +
      ((-1) * aMask a side 19) +
      (2 * aMask a side 20) +
      (2 * aMask a side 21) +
      ((-1) * aMask a side 22) +
      ((-1) * aMask a side 23) +
      (2 * aMask a side 24) +
      (2 * aMask a side 25) +
      ((-1) * aMask a side 26) +
      ((-1) * aMask a side 27) +
      (2 * aMask a side 28) +
      (2 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_2_0,
      maskKrawtchoukCoeff_2_1,
      maskKrawtchoukCoeff_2_2,
      maskKrawtchoukCoeff_2_3,
      maskKrawtchoukCoeff_2_4,
      maskKrawtchoukCoeff_2_5,
      maskKrawtchoukCoeff_2_6,
      maskKrawtchoukCoeff_2_7,
      maskKrawtchoukCoeff_2_8,
      maskKrawtchoukCoeff_2_9,
      maskKrawtchoukCoeff_2_10,
      maskKrawtchoukCoeff_2_11,
      maskKrawtchoukCoeff_2_12,
      maskKrawtchoukCoeff_2_13,
      maskKrawtchoukCoeff_2_14,
      maskKrawtchoukCoeff_2_15,
      maskKrawtchoukCoeff_2_16,
      maskKrawtchoukCoeff_2_17,
      maskKrawtchoukCoeff_2_18,
      maskKrawtchoukCoeff_2_19,
      maskKrawtchoukCoeff_2_20,
      maskKrawtchoukCoeff_2_21,
      maskKrawtchoukCoeff_2_22,
      maskKrawtchoukCoeff_2_23,
      maskKrawtchoukCoeff_2_24,
      maskKrawtchoukCoeff_2_25,
      maskKrawtchoukCoeff_2_26,
      maskKrawtchoukCoeff_2_27,
      maskKrawtchoukCoeff_2_28,
      maskKrawtchoukCoeff_2_29,
      maskKrawtchoukCoeff_2_30,
      maskKrawtchoukCoeff_2_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 3. -/
theorem multiaxisEnergy_aMask_row_3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 3) =
      (2 * aMask a side 0) +
      ((-2) * aMask a side 1) +
      ((-1) * aMask a side 2) +
      (1 * aMask a side 3) +
      (2 * aMask a side 4) +
      ((-2) * aMask a side 5) +
      ((-1) * aMask a side 6) +
      (1 * aMask a side 7) +
      (2 * aMask a side 8) +
      ((-2) * aMask a side 9) +
      ((-1) * aMask a side 10) +
      (1 * aMask a side 11) +
      (2 * aMask a side 12) +
      ((-2) * aMask a side 13) +
      ((-1) * aMask a side 14) +
      (1 * aMask a side 15) +
      (2 * aMask a side 16) +
      ((-2) * aMask a side 17) +
      ((-1) * aMask a side 18) +
      (1 * aMask a side 19) +
      (2 * aMask a side 20) +
      ((-2) * aMask a side 21) +
      ((-1) * aMask a side 22) +
      (1 * aMask a side 23) +
      (2 * aMask a side 24) +
      ((-2) * aMask a side 25) +
      ((-1) * aMask a side 26) +
      (1 * aMask a side 27) +
      (2 * aMask a side 28) +
      ((-2) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_3_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 4. -/
theorem multiaxisEnergy_aMask_row_4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 4) =
      (4 * aMask a side 0) +
      (4 * aMask a side 1) +
      (4 * aMask a side 2) +
      (4 * aMask a side 3) +
      ((-1) * aMask a side 4) +
      ((-1) * aMask a side 5) +
      ((-1) * aMask a side 6) +
      ((-1) * aMask a side 7) +
      (4 * aMask a side 8) +
      (4 * aMask a side 9) +
      (4 * aMask a side 10) +
      (4 * aMask a side 11) +
      ((-1) * aMask a side 12) +
      ((-1) * aMask a side 13) +
      ((-1) * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (4 * aMask a side 16) +
      (4 * aMask a side 17) +
      (4 * aMask a side 18) +
      (4 * aMask a side 19) +
      ((-1) * aMask a side 20) +
      ((-1) * aMask a side 21) +
      ((-1) * aMask a side 22) +
      ((-1) * aMask a side 23) +
      (4 * aMask a side 24) +
      (4 * aMask a side 25) +
      (4 * aMask a side 26) +
      (4 * aMask a side 27) +
      ((-1) * aMask a side 28) +
      ((-1) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_4_0,
      maskKrawtchoukCoeff_4_1,
      maskKrawtchoukCoeff_4_2,
      maskKrawtchoukCoeff_4_3,
      maskKrawtchoukCoeff_4_4,
      maskKrawtchoukCoeff_4_5,
      maskKrawtchoukCoeff_4_6,
      maskKrawtchoukCoeff_4_7,
      maskKrawtchoukCoeff_4_8,
      maskKrawtchoukCoeff_4_9,
      maskKrawtchoukCoeff_4_10,
      maskKrawtchoukCoeff_4_11,
      maskKrawtchoukCoeff_4_12,
      maskKrawtchoukCoeff_4_13,
      maskKrawtchoukCoeff_4_14,
      maskKrawtchoukCoeff_4_15,
      maskKrawtchoukCoeff_4_16,
      maskKrawtchoukCoeff_4_17,
      maskKrawtchoukCoeff_4_18,
      maskKrawtchoukCoeff_4_19,
      maskKrawtchoukCoeff_4_20,
      maskKrawtchoukCoeff_4_21,
      maskKrawtchoukCoeff_4_22,
      maskKrawtchoukCoeff_4_23,
      maskKrawtchoukCoeff_4_24,
      maskKrawtchoukCoeff_4_25,
      maskKrawtchoukCoeff_4_26,
      maskKrawtchoukCoeff_4_27,
      maskKrawtchoukCoeff_4_28,
      maskKrawtchoukCoeff_4_29,
      maskKrawtchoukCoeff_4_30,
      maskKrawtchoukCoeff_4_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 5. -/
theorem multiaxisEnergy_aMask_row_5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 5) =
      (4 * aMask a side 0) +
      ((-4) * aMask a side 1) +
      (4 * aMask a side 2) +
      ((-4) * aMask a side 3) +
      ((-1) * aMask a side 4) +
      (1 * aMask a side 5) +
      ((-1) * aMask a side 6) +
      (1 * aMask a side 7) +
      (4 * aMask a side 8) +
      ((-4) * aMask a side 9) +
      (4 * aMask a side 10) +
      ((-4) * aMask a side 11) +
      ((-1) * aMask a side 12) +
      (1 * aMask a side 13) +
      ((-1) * aMask a side 14) +
      (1 * aMask a side 15) +
      (4 * aMask a side 16) +
      ((-4) * aMask a side 17) +
      (4 * aMask a side 18) +
      ((-4) * aMask a side 19) +
      ((-1) * aMask a side 20) +
      (1 * aMask a side 21) +
      ((-1) * aMask a side 22) +
      (1 * aMask a side 23) +
      (4 * aMask a side 24) +
      ((-4) * aMask a side 25) +
      (4 * aMask a side 26) +
      ((-4) * aMask a side 27) +
      ((-1) * aMask a side 28) +
      (1 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_5_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 6. -/
theorem multiaxisEnergy_aMask_row_6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 6) =
      (8 * aMask a side 0) +
      (8 * aMask a side 1) +
      ((-4) * aMask a side 2) +
      ((-4) * aMask a side 3) +
      ((-2) * aMask a side 4) +
      ((-2) * aMask a side 5) +
      (1 * aMask a side 6) +
      (1 * aMask a side 7) +
      (8 * aMask a side 8) +
      (8 * aMask a side 9) +
      ((-4) * aMask a side 10) +
      ((-4) * aMask a side 11) +
      ((-2) * aMask a side 12) +
      ((-2) * aMask a side 13) +
      (1 * aMask a side 14) +
      (1 * aMask a side 15) +
      (8 * aMask a side 16) +
      (8 * aMask a side 17) +
      ((-4) * aMask a side 18) +
      ((-4) * aMask a side 19) +
      ((-2) * aMask a side 20) +
      ((-2) * aMask a side 21) +
      (1 * aMask a side 22) +
      (1 * aMask a side 23) +
      (8 * aMask a side 24) +
      (8 * aMask a side 25) +
      ((-4) * aMask a side 26) +
      ((-4) * aMask a side 27) +
      ((-2) * aMask a side 28) +
      ((-2) * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_6_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 7. -/
theorem multiaxisEnergy_aMask_row_7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 7) =
      (8 * aMask a side 0) +
      ((-8) * aMask a side 1) +
      ((-4) * aMask a side 2) +
      (4 * aMask a side 3) +
      ((-2) * aMask a side 4) +
      (2 * aMask a side 5) +
      (1 * aMask a side 6) +
      ((-1) * aMask a side 7) +
      (8 * aMask a side 8) +
      ((-8) * aMask a side 9) +
      ((-4) * aMask a side 10) +
      (4 * aMask a side 11) +
      ((-2) * aMask a side 12) +
      (2 * aMask a side 13) +
      (1 * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (8 * aMask a side 16) +
      ((-8) * aMask a side 17) +
      ((-4) * aMask a side 18) +
      (4 * aMask a side 19) +
      ((-2) * aMask a side 20) +
      (2 * aMask a side 21) +
      (1 * aMask a side 22) +
      ((-1) * aMask a side 23) +
      (8 * aMask a side 24) +
      ((-8) * aMask a side 25) +
      ((-4) * aMask a side 26) +
      (4 * aMask a side 27) +
      ((-2) * aMask a side 28) +
      (2 * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_7_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 8. -/
theorem multiaxisEnergy_aMask_row_8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 8) =
      (6 * aMask a side 0) +
      (6 * aMask a side 1) +
      (6 * aMask a side 2) +
      (6 * aMask a side 3) +
      (6 * aMask a side 4) +
      (6 * aMask a side 5) +
      (6 * aMask a side 6) +
      (6 * aMask a side 7) +
      ((-1) * aMask a side 8) +
      ((-1) * aMask a side 9) +
      ((-1) * aMask a side 10) +
      ((-1) * aMask a side 11) +
      ((-1) * aMask a side 12) +
      ((-1) * aMask a side 13) +
      ((-1) * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (6 * aMask a side 16) +
      (6 * aMask a side 17) +
      (6 * aMask a side 18) +
      (6 * aMask a side 19) +
      (6 * aMask a side 20) +
      (6 * aMask a side 21) +
      (6 * aMask a side 22) +
      (6 * aMask a side 23) +
      ((-1) * aMask a side 24) +
      ((-1) * aMask a side 25) +
      ((-1) * aMask a side 26) +
      ((-1) * aMask a side 27) +
      ((-1) * aMask a side 28) +
      ((-1) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_8_0,
      maskKrawtchoukCoeff_8_1,
      maskKrawtchoukCoeff_8_2,
      maskKrawtchoukCoeff_8_3,
      maskKrawtchoukCoeff_8_4,
      maskKrawtchoukCoeff_8_5,
      maskKrawtchoukCoeff_8_6,
      maskKrawtchoukCoeff_8_7,
      maskKrawtchoukCoeff_8_8,
      maskKrawtchoukCoeff_8_9,
      maskKrawtchoukCoeff_8_10,
      maskKrawtchoukCoeff_8_11,
      maskKrawtchoukCoeff_8_12,
      maskKrawtchoukCoeff_8_13,
      maskKrawtchoukCoeff_8_14,
      maskKrawtchoukCoeff_8_15,
      maskKrawtchoukCoeff_8_16,
      maskKrawtchoukCoeff_8_17,
      maskKrawtchoukCoeff_8_18,
      maskKrawtchoukCoeff_8_19,
      maskKrawtchoukCoeff_8_20,
      maskKrawtchoukCoeff_8_21,
      maskKrawtchoukCoeff_8_22,
      maskKrawtchoukCoeff_8_23,
      maskKrawtchoukCoeff_8_24,
      maskKrawtchoukCoeff_8_25,
      maskKrawtchoukCoeff_8_26,
      maskKrawtchoukCoeff_8_27,
      maskKrawtchoukCoeff_8_28,
      maskKrawtchoukCoeff_8_29,
      maskKrawtchoukCoeff_8_30,
      maskKrawtchoukCoeff_8_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 9. -/
theorem multiaxisEnergy_aMask_row_9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 9) =
      (6 * aMask a side 0) +
      ((-6) * aMask a side 1) +
      (6 * aMask a side 2) +
      ((-6) * aMask a side 3) +
      (6 * aMask a side 4) +
      ((-6) * aMask a side 5) +
      (6 * aMask a side 6) +
      ((-6) * aMask a side 7) +
      ((-1) * aMask a side 8) +
      (1 * aMask a side 9) +
      ((-1) * aMask a side 10) +
      (1 * aMask a side 11) +
      ((-1) * aMask a side 12) +
      (1 * aMask a side 13) +
      ((-1) * aMask a side 14) +
      (1 * aMask a side 15) +
      (6 * aMask a side 16) +
      ((-6) * aMask a side 17) +
      (6 * aMask a side 18) +
      ((-6) * aMask a side 19) +
      (6 * aMask a side 20) +
      ((-6) * aMask a side 21) +
      (6 * aMask a side 22) +
      ((-6) * aMask a side 23) +
      ((-1) * aMask a side 24) +
      (1 * aMask a side 25) +
      ((-1) * aMask a side 26) +
      (1 * aMask a side 27) +
      ((-1) * aMask a side 28) +
      (1 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_9_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 10. -/
theorem multiaxisEnergy_aMask_row_10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 10) =
      (12 * aMask a side 0) +
      (12 * aMask a side 1) +
      ((-6) * aMask a side 2) +
      ((-6) * aMask a side 3) +
      (12 * aMask a side 4) +
      (12 * aMask a side 5) +
      ((-6) * aMask a side 6) +
      ((-6) * aMask a side 7) +
      ((-2) * aMask a side 8) +
      ((-2) * aMask a side 9) +
      (1 * aMask a side 10) +
      (1 * aMask a side 11) +
      ((-2) * aMask a side 12) +
      ((-2) * aMask a side 13) +
      (1 * aMask a side 14) +
      (1 * aMask a side 15) +
      (12 * aMask a side 16) +
      (12 * aMask a side 17) +
      ((-6) * aMask a side 18) +
      ((-6) * aMask a side 19) +
      (12 * aMask a side 20) +
      (12 * aMask a side 21) +
      ((-6) * aMask a side 22) +
      ((-6) * aMask a side 23) +
      ((-2) * aMask a side 24) +
      ((-2) * aMask a side 25) +
      (1 * aMask a side 26) +
      (1 * aMask a side 27) +
      ((-2) * aMask a side 28) +
      ((-2) * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_10_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 11. -/
theorem multiaxisEnergy_aMask_row_11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 11) =
      (12 * aMask a side 0) +
      ((-12) * aMask a side 1) +
      ((-6) * aMask a side 2) +
      (6 * aMask a side 3) +
      (12 * aMask a side 4) +
      ((-12) * aMask a side 5) +
      ((-6) * aMask a side 6) +
      (6 * aMask a side 7) +
      ((-2) * aMask a side 8) +
      (2 * aMask a side 9) +
      (1 * aMask a side 10) +
      ((-1) * aMask a side 11) +
      ((-2) * aMask a side 12) +
      (2 * aMask a side 13) +
      (1 * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (12 * aMask a side 16) +
      ((-12) * aMask a side 17) +
      ((-6) * aMask a side 18) +
      (6 * aMask a side 19) +
      (12 * aMask a side 20) +
      ((-12) * aMask a side 21) +
      ((-6) * aMask a side 22) +
      (6 * aMask a side 23) +
      ((-2) * aMask a side 24) +
      (2 * aMask a side 25) +
      (1 * aMask a side 26) +
      ((-1) * aMask a side 27) +
      ((-2) * aMask a side 28) +
      (2 * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_11_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 12. -/
theorem multiaxisEnergy_aMask_row_12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 12) =
      (24 * aMask a side 0) +
      (24 * aMask a side 1) +
      (24 * aMask a side 2) +
      (24 * aMask a side 3) +
      ((-6) * aMask a side 4) +
      ((-6) * aMask a side 5) +
      ((-6) * aMask a side 6) +
      ((-6) * aMask a side 7) +
      ((-4) * aMask a side 8) +
      ((-4) * aMask a side 9) +
      ((-4) * aMask a side 10) +
      ((-4) * aMask a side 11) +
      (1 * aMask a side 12) +
      (1 * aMask a side 13) +
      (1 * aMask a side 14) +
      (1 * aMask a side 15) +
      (24 * aMask a side 16) +
      (24 * aMask a side 17) +
      (24 * aMask a side 18) +
      (24 * aMask a side 19) +
      ((-6) * aMask a side 20) +
      ((-6) * aMask a side 21) +
      ((-6) * aMask a side 22) +
      ((-6) * aMask a side 23) +
      ((-4) * aMask a side 24) +
      ((-4) * aMask a side 25) +
      ((-4) * aMask a side 26) +
      ((-4) * aMask a side 27) +
      (1 * aMask a side 28) +
      (1 * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_12_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 13. -/
theorem multiaxisEnergy_aMask_row_13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 13) =
      (24 * aMask a side 0) +
      ((-24) * aMask a side 1) +
      (24 * aMask a side 2) +
      ((-24) * aMask a side 3) +
      ((-6) * aMask a side 4) +
      (6 * aMask a side 5) +
      ((-6) * aMask a side 6) +
      (6 * aMask a side 7) +
      ((-4) * aMask a side 8) +
      (4 * aMask a side 9) +
      ((-4) * aMask a side 10) +
      (4 * aMask a side 11) +
      (1 * aMask a side 12) +
      ((-1) * aMask a side 13) +
      (1 * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (24 * aMask a side 16) +
      ((-24) * aMask a side 17) +
      (24 * aMask a side 18) +
      ((-24) * aMask a side 19) +
      ((-6) * aMask a side 20) +
      (6 * aMask a side 21) +
      ((-6) * aMask a side 22) +
      (6 * aMask a side 23) +
      ((-4) * aMask a side 24) +
      (4 * aMask a side 25) +
      ((-4) * aMask a side 26) +
      (4 * aMask a side 27) +
      (1 * aMask a side 28) +
      ((-1) * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_13_0,
      maskKrawtchoukCoeff_13_1,
      maskKrawtchoukCoeff_13_2,
      maskKrawtchoukCoeff_13_3,
      maskKrawtchoukCoeff_13_4,
      maskKrawtchoukCoeff_13_5,
      maskKrawtchoukCoeff_13_6,
      maskKrawtchoukCoeff_13_7,
      maskKrawtchoukCoeff_13_8,
      maskKrawtchoukCoeff_13_9,
      maskKrawtchoukCoeff_13_10,
      maskKrawtchoukCoeff_13_11,
      maskKrawtchoukCoeff_13_12,
      maskKrawtchoukCoeff_13_13,
      maskKrawtchoukCoeff_13_14,
      maskKrawtchoukCoeff_13_15,
      maskKrawtchoukCoeff_13_16,
      maskKrawtchoukCoeff_13_17,
      maskKrawtchoukCoeff_13_18,
      maskKrawtchoukCoeff_13_19,
      maskKrawtchoukCoeff_13_20,
      maskKrawtchoukCoeff_13_21,
      maskKrawtchoukCoeff_13_22,
      maskKrawtchoukCoeff_13_23,
      maskKrawtchoukCoeff_13_24,
      maskKrawtchoukCoeff_13_25,
      maskKrawtchoukCoeff_13_26,
      maskKrawtchoukCoeff_13_27,
      maskKrawtchoukCoeff_13_28,
      maskKrawtchoukCoeff_13_29,
      maskKrawtchoukCoeff_13_30,
      maskKrawtchoukCoeff_13_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 14. -/
theorem multiaxisEnergy_aMask_row_14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 14) =
      (48 * aMask a side 0) +
      (48 * aMask a side 1) +
      ((-24) * aMask a side 2) +
      ((-24) * aMask a side 3) +
      ((-12) * aMask a side 4) +
      ((-12) * aMask a side 5) +
      (6 * aMask a side 6) +
      (6 * aMask a side 7) +
      ((-8) * aMask a side 8) +
      ((-8) * aMask a side 9) +
      (4 * aMask a side 10) +
      (4 * aMask a side 11) +
      (2 * aMask a side 12) +
      (2 * aMask a side 13) +
      ((-1) * aMask a side 14) +
      ((-1) * aMask a side 15) +
      (48 * aMask a side 16) +
      (48 * aMask a side 17) +
      ((-24) * aMask a side 18) +
      ((-24) * aMask a side 19) +
      ((-12) * aMask a side 20) +
      ((-12) * aMask a side 21) +
      (6 * aMask a side 22) +
      (6 * aMask a side 23) +
      ((-8) * aMask a side 24) +
      ((-8) * aMask a side 25) +
      (4 * aMask a side 26) +
      (4 * aMask a side 27) +
      (2 * aMask a side 28) +
      (2 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_14_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 15. -/
theorem multiaxisEnergy_aMask_row_15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 15) =
      (48 * aMask a side 0) +
      ((-48) * aMask a side 1) +
      ((-24) * aMask a side 2) +
      (24 * aMask a side 3) +
      ((-12) * aMask a side 4) +
      (12 * aMask a side 5) +
      (6 * aMask a side 6) +
      ((-6) * aMask a side 7) +
      ((-8) * aMask a side 8) +
      (8 * aMask a side 9) +
      (4 * aMask a side 10) +
      ((-4) * aMask a side 11) +
      (2 * aMask a side 12) +
      ((-2) * aMask a side 13) +
      ((-1) * aMask a side 14) +
      (1 * aMask a side 15) +
      (48 * aMask a side 16) +
      ((-48) * aMask a side 17) +
      ((-24) * aMask a side 18) +
      (24 * aMask a side 19) +
      ((-12) * aMask a side 20) +
      (12 * aMask a side 21) +
      (6 * aMask a side 22) +
      ((-6) * aMask a side 23) +
      ((-8) * aMask a side 24) +
      (8 * aMask a side 25) +
      (4 * aMask a side 26) +
      ((-4) * aMask a side 27) +
      (2 * aMask a side 28) +
      ((-2) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_15_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 16. -/
theorem multiaxisEnergy_aMask_row_16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 16) =
      (10 * aMask a side 0) +
      (10 * aMask a side 1) +
      (10 * aMask a side 2) +
      (10 * aMask a side 3) +
      (10 * aMask a side 4) +
      (10 * aMask a side 5) +
      (10 * aMask a side 6) +
      (10 * aMask a side 7) +
      (10 * aMask a side 8) +
      (10 * aMask a side 9) +
      (10 * aMask a side 10) +
      (10 * aMask a side 11) +
      (10 * aMask a side 12) +
      (10 * aMask a side 13) +
      (10 * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-1) * aMask a side 16) +
      ((-1) * aMask a side 17) +
      ((-1) * aMask a side 18) +
      ((-1) * aMask a side 19) +
      ((-1) * aMask a side 20) +
      ((-1) * aMask a side 21) +
      ((-1) * aMask a side 22) +
      ((-1) * aMask a side 23) +
      ((-1) * aMask a side 24) +
      ((-1) * aMask a side 25) +
      ((-1) * aMask a side 26) +
      ((-1) * aMask a side 27) +
      ((-1) * aMask a side 28) +
      ((-1) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_16_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 17. -/
theorem multiaxisEnergy_aMask_row_17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 17) =
      (10 * aMask a side 0) +
      ((-10) * aMask a side 1) +
      (10 * aMask a side 2) +
      ((-10) * aMask a side 3) +
      (10 * aMask a side 4) +
      ((-10) * aMask a side 5) +
      (10 * aMask a side 6) +
      ((-10) * aMask a side 7) +
      (10 * aMask a side 8) +
      ((-10) * aMask a side 9) +
      (10 * aMask a side 10) +
      ((-10) * aMask a side 11) +
      (10 * aMask a side 12) +
      ((-10) * aMask a side 13) +
      (10 * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-1) * aMask a side 16) +
      (1 * aMask a side 17) +
      ((-1) * aMask a side 18) +
      (1 * aMask a side 19) +
      ((-1) * aMask a side 20) +
      (1 * aMask a side 21) +
      ((-1) * aMask a side 22) +
      (1 * aMask a side 23) +
      ((-1) * aMask a side 24) +
      (1 * aMask a side 25) +
      ((-1) * aMask a side 26) +
      (1 * aMask a side 27) +
      ((-1) * aMask a side 28) +
      (1 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_17_0,
      maskKrawtchoukCoeff_17_1,
      maskKrawtchoukCoeff_17_2,
      maskKrawtchoukCoeff_17_3,
      maskKrawtchoukCoeff_17_4,
      maskKrawtchoukCoeff_17_5,
      maskKrawtchoukCoeff_17_6,
      maskKrawtchoukCoeff_17_7,
      maskKrawtchoukCoeff_17_8,
      maskKrawtchoukCoeff_17_9,
      maskKrawtchoukCoeff_17_10,
      maskKrawtchoukCoeff_17_11,
      maskKrawtchoukCoeff_17_12,
      maskKrawtchoukCoeff_17_13,
      maskKrawtchoukCoeff_17_14,
      maskKrawtchoukCoeff_17_15,
      maskKrawtchoukCoeff_17_16,
      maskKrawtchoukCoeff_17_17,
      maskKrawtchoukCoeff_17_18,
      maskKrawtchoukCoeff_17_19,
      maskKrawtchoukCoeff_17_20,
      maskKrawtchoukCoeff_17_21,
      maskKrawtchoukCoeff_17_22,
      maskKrawtchoukCoeff_17_23,
      maskKrawtchoukCoeff_17_24,
      maskKrawtchoukCoeff_17_25,
      maskKrawtchoukCoeff_17_26,
      maskKrawtchoukCoeff_17_27,
      maskKrawtchoukCoeff_17_28,
      maskKrawtchoukCoeff_17_29,
      maskKrawtchoukCoeff_17_30,
      maskKrawtchoukCoeff_17_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 18. -/
theorem multiaxisEnergy_aMask_row_18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 18) =
      (20 * aMask a side 0) +
      (20 * aMask a side 1) +
      ((-10) * aMask a side 2) +
      ((-10) * aMask a side 3) +
      (20 * aMask a side 4) +
      (20 * aMask a side 5) +
      ((-10) * aMask a side 6) +
      ((-10) * aMask a side 7) +
      (20 * aMask a side 8) +
      (20 * aMask a side 9) +
      ((-10) * aMask a side 10) +
      ((-10) * aMask a side 11) +
      (20 * aMask a side 12) +
      (20 * aMask a side 13) +
      ((-10) * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-2) * aMask a side 16) +
      ((-2) * aMask a side 17) +
      (1 * aMask a side 18) +
      (1 * aMask a side 19) +
      ((-2) * aMask a side 20) +
      ((-2) * aMask a side 21) +
      (1 * aMask a side 22) +
      (1 * aMask a side 23) +
      ((-2) * aMask a side 24) +
      ((-2) * aMask a side 25) +
      (1 * aMask a side 26) +
      (1 * aMask a side 27) +
      ((-2) * aMask a side 28) +
      ((-2) * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_18_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 19. -/
theorem multiaxisEnergy_aMask_row_19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 19) =
      (20 * aMask a side 0) +
      ((-20) * aMask a side 1) +
      ((-10) * aMask a side 2) +
      (10 * aMask a side 3) +
      (20 * aMask a side 4) +
      ((-20) * aMask a side 5) +
      ((-10) * aMask a side 6) +
      (10 * aMask a side 7) +
      (20 * aMask a side 8) +
      ((-20) * aMask a side 9) +
      ((-10) * aMask a side 10) +
      (10 * aMask a side 11) +
      (20 * aMask a side 12) +
      ((-20) * aMask a side 13) +
      ((-10) * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-2) * aMask a side 16) +
      (2 * aMask a side 17) +
      (1 * aMask a side 18) +
      ((-1) * aMask a side 19) +
      ((-2) * aMask a side 20) +
      (2 * aMask a side 21) +
      (1 * aMask a side 22) +
      ((-1) * aMask a side 23) +
      ((-2) * aMask a side 24) +
      (2 * aMask a side 25) +
      (1 * aMask a side 26) +
      ((-1) * aMask a side 27) +
      ((-2) * aMask a side 28) +
      (2 * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_19_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 20. -/
theorem multiaxisEnergy_aMask_row_20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 20) =
      (40 * aMask a side 0) +
      (40 * aMask a side 1) +
      (40 * aMask a side 2) +
      (40 * aMask a side 3) +
      ((-10) * aMask a side 4) +
      ((-10) * aMask a side 5) +
      ((-10) * aMask a side 6) +
      ((-10) * aMask a side 7) +
      (40 * aMask a side 8) +
      (40 * aMask a side 9) +
      (40 * aMask a side 10) +
      (40 * aMask a side 11) +
      ((-10) * aMask a side 12) +
      ((-10) * aMask a side 13) +
      ((-10) * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-4) * aMask a side 16) +
      ((-4) * aMask a side 17) +
      ((-4) * aMask a side 18) +
      ((-4) * aMask a side 19) +
      (1 * aMask a side 20) +
      (1 * aMask a side 21) +
      (1 * aMask a side 22) +
      (1 * aMask a side 23) +
      ((-4) * aMask a side 24) +
      ((-4) * aMask a side 25) +
      ((-4) * aMask a side 26) +
      ((-4) * aMask a side 27) +
      (1 * aMask a side 28) +
      (1 * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_20_0,
      maskKrawtchoukCoeff_20_1,
      maskKrawtchoukCoeff_20_2,
      maskKrawtchoukCoeff_20_3,
      maskKrawtchoukCoeff_20_4,
      maskKrawtchoukCoeff_20_5,
      maskKrawtchoukCoeff_20_6,
      maskKrawtchoukCoeff_20_7,
      maskKrawtchoukCoeff_20_8,
      maskKrawtchoukCoeff_20_9,
      maskKrawtchoukCoeff_20_10,
      maskKrawtchoukCoeff_20_11,
      maskKrawtchoukCoeff_20_12,
      maskKrawtchoukCoeff_20_13,
      maskKrawtchoukCoeff_20_14,
      maskKrawtchoukCoeff_20_15,
      maskKrawtchoukCoeff_20_16,
      maskKrawtchoukCoeff_20_17,
      maskKrawtchoukCoeff_20_18,
      maskKrawtchoukCoeff_20_19,
      maskKrawtchoukCoeff_20_20,
      maskKrawtchoukCoeff_20_21,
      maskKrawtchoukCoeff_20_22,
      maskKrawtchoukCoeff_20_23,
      maskKrawtchoukCoeff_20_24,
      maskKrawtchoukCoeff_20_25,
      maskKrawtchoukCoeff_20_26,
      maskKrawtchoukCoeff_20_27,
      maskKrawtchoukCoeff_20_28,
      maskKrawtchoukCoeff_20_29,
      maskKrawtchoukCoeff_20_30,
      maskKrawtchoukCoeff_20_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 21. -/
theorem multiaxisEnergy_aMask_row_21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 21) =
      (40 * aMask a side 0) +
      ((-40) * aMask a side 1) +
      (40 * aMask a side 2) +
      ((-40) * aMask a side 3) +
      ((-10) * aMask a side 4) +
      (10 * aMask a side 5) +
      ((-10) * aMask a side 6) +
      (10 * aMask a side 7) +
      (40 * aMask a side 8) +
      ((-40) * aMask a side 9) +
      (40 * aMask a side 10) +
      ((-40) * aMask a side 11) +
      ((-10) * aMask a side 12) +
      (10 * aMask a side 13) +
      ((-10) * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-4) * aMask a side 16) +
      (4 * aMask a side 17) +
      ((-4) * aMask a side 18) +
      (4 * aMask a side 19) +
      (1 * aMask a side 20) +
      ((-1) * aMask a side 21) +
      (1 * aMask a side 22) +
      ((-1) * aMask a side 23) +
      ((-4) * aMask a side 24) +
      (4 * aMask a side 25) +
      ((-4) * aMask a side 26) +
      (4 * aMask a side 27) +
      (1 * aMask a side 28) +
      ((-1) * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_21_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 22. -/
theorem multiaxisEnergy_aMask_row_22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 22) =
      (80 * aMask a side 0) +
      (80 * aMask a side 1) +
      ((-40) * aMask a side 2) +
      ((-40) * aMask a side 3) +
      ((-20) * aMask a side 4) +
      ((-20) * aMask a side 5) +
      (10 * aMask a side 6) +
      (10 * aMask a side 7) +
      (80 * aMask a side 8) +
      (80 * aMask a side 9) +
      ((-40) * aMask a side 10) +
      ((-40) * aMask a side 11) +
      ((-20) * aMask a side 12) +
      ((-20) * aMask a side 13) +
      (10 * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-8) * aMask a side 16) +
      ((-8) * aMask a side 17) +
      (4 * aMask a side 18) +
      (4 * aMask a side 19) +
      (2 * aMask a side 20) +
      (2 * aMask a side 21) +
      ((-1) * aMask a side 22) +
      ((-1) * aMask a side 23) +
      ((-8) * aMask a side 24) +
      ((-8) * aMask a side 25) +
      (4 * aMask a side 26) +
      (4 * aMask a side 27) +
      (2 * aMask a side 28) +
      (2 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_22_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 23. -/
theorem multiaxisEnergy_aMask_row_23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 23) =
      (80 * aMask a side 0) +
      ((-80) * aMask a side 1) +
      ((-40) * aMask a side 2) +
      (40 * aMask a side 3) +
      ((-20) * aMask a side 4) +
      (20 * aMask a side 5) +
      (10 * aMask a side 6) +
      ((-10) * aMask a side 7) +
      (80 * aMask a side 8) +
      ((-80) * aMask a side 9) +
      ((-40) * aMask a side 10) +
      (40 * aMask a side 11) +
      ((-20) * aMask a side 12) +
      (20 * aMask a side 13) +
      (10 * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-8) * aMask a side 16) +
      (8 * aMask a side 17) +
      (4 * aMask a side 18) +
      ((-4) * aMask a side 19) +
      (2 * aMask a side 20) +
      ((-2) * aMask a side 21) +
      ((-1) * aMask a side 22) +
      (1 * aMask a side 23) +
      ((-8) * aMask a side 24) +
      (8 * aMask a side 25) +
      (4 * aMask a side 26) +
      ((-4) * aMask a side 27) +
      (2 * aMask a side 28) +
      ((-2) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_23_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 24. -/
theorem multiaxisEnergy_aMask_row_24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 24) =
      (60 * aMask a side 0) +
      (60 * aMask a side 1) +
      (60 * aMask a side 2) +
      (60 * aMask a side 3) +
      (60 * aMask a side 4) +
      (60 * aMask a side 5) +
      (60 * aMask a side 6) +
      (60 * aMask a side 7) +
      ((-10) * aMask a side 8) +
      ((-10) * aMask a side 9) +
      ((-10) * aMask a side 10) +
      ((-10) * aMask a side 11) +
      ((-10) * aMask a side 12) +
      ((-10) * aMask a side 13) +
      ((-10) * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-6) * aMask a side 16) +
      ((-6) * aMask a side 17) +
      ((-6) * aMask a side 18) +
      ((-6) * aMask a side 19) +
      ((-6) * aMask a side 20) +
      ((-6) * aMask a side 21) +
      ((-6) * aMask a side 22) +
      ((-6) * aMask a side 23) +
      (1 * aMask a side 24) +
      (1 * aMask a side 25) +
      (1 * aMask a side 26) +
      (1 * aMask a side 27) +
      (1 * aMask a side 28) +
      (1 * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_24_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 25. -/
theorem multiaxisEnergy_aMask_row_25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 25) =
      (60 * aMask a side 0) +
      ((-60) * aMask a side 1) +
      (60 * aMask a side 2) +
      ((-60) * aMask a side 3) +
      (60 * aMask a side 4) +
      ((-60) * aMask a side 5) +
      (60 * aMask a side 6) +
      ((-60) * aMask a side 7) +
      ((-10) * aMask a side 8) +
      (10 * aMask a side 9) +
      ((-10) * aMask a side 10) +
      (10 * aMask a side 11) +
      ((-10) * aMask a side 12) +
      (10 * aMask a side 13) +
      ((-10) * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-6) * aMask a side 16) +
      (6 * aMask a side 17) +
      ((-6) * aMask a side 18) +
      (6 * aMask a side 19) +
      ((-6) * aMask a side 20) +
      (6 * aMask a side 21) +
      ((-6) * aMask a side 22) +
      (6 * aMask a side 23) +
      (1 * aMask a side 24) +
      ((-1) * aMask a side 25) +
      (1 * aMask a side 26) +
      ((-1) * aMask a side 27) +
      (1 * aMask a side 28) +
      ((-1) * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_25_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 26. -/
theorem multiaxisEnergy_aMask_row_26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 26) =
      (120 * aMask a side 0) +
      (120 * aMask a side 1) +
      ((-60) * aMask a side 2) +
      ((-60) * aMask a side 3) +
      (120 * aMask a side 4) +
      (120 * aMask a side 5) +
      ((-60) * aMask a side 6) +
      ((-60) * aMask a side 7) +
      ((-20) * aMask a side 8) +
      ((-20) * aMask a side 9) +
      (10 * aMask a side 10) +
      (10 * aMask a side 11) +
      ((-20) * aMask a side 12) +
      ((-20) * aMask a side 13) +
      (10 * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-12) * aMask a side 16) +
      ((-12) * aMask a side 17) +
      (6 * aMask a side 18) +
      (6 * aMask a side 19) +
      ((-12) * aMask a side 20) +
      ((-12) * aMask a side 21) +
      (6 * aMask a side 22) +
      (6 * aMask a side 23) +
      (2 * aMask a side 24) +
      (2 * aMask a side 25) +
      ((-1) * aMask a side 26) +
      ((-1) * aMask a side 27) +
      (2 * aMask a side 28) +
      (2 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_26_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 27. -/
theorem multiaxisEnergy_aMask_row_27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 27) =
      (120 * aMask a side 0) +
      ((-120) * aMask a side 1) +
      ((-60) * aMask a side 2) +
      (60 * aMask a side 3) +
      (120 * aMask a side 4) +
      ((-120) * aMask a side 5) +
      ((-60) * aMask a side 6) +
      (60 * aMask a side 7) +
      ((-20) * aMask a side 8) +
      (20 * aMask a side 9) +
      (10 * aMask a side 10) +
      ((-10) * aMask a side 11) +
      ((-20) * aMask a side 12) +
      (20 * aMask a side 13) +
      (10 * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-12) * aMask a side 16) +
      (12 * aMask a side 17) +
      (6 * aMask a side 18) +
      ((-6) * aMask a side 19) +
      ((-12) * aMask a side 20) +
      (12 * aMask a side 21) +
      (6 * aMask a side 22) +
      ((-6) * aMask a side 23) +
      (2 * aMask a side 24) +
      ((-2) * aMask a side 25) +
      ((-1) * aMask a side 26) +
      (1 * aMask a side 27) +
      (2 * aMask a side 28) +
      ((-2) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
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
      maskKrawtchoukCoeff_27_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 28. -/
theorem multiaxisEnergy_aMask_row_28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 28) =
      (240 * aMask a side 0) +
      (240 * aMask a side 1) +
      (240 * aMask a side 2) +
      (240 * aMask a side 3) +
      ((-60) * aMask a side 4) +
      ((-60) * aMask a side 5) +
      ((-60) * aMask a side 6) +
      ((-60) * aMask a side 7) +
      ((-40) * aMask a side 8) +
      ((-40) * aMask a side 9) +
      ((-40) * aMask a side 10) +
      ((-40) * aMask a side 11) +
      (10 * aMask a side 12) +
      (10 * aMask a side 13) +
      (10 * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-24) * aMask a side 16) +
      ((-24) * aMask a side 17) +
      ((-24) * aMask a side 18) +
      ((-24) * aMask a side 19) +
      (6 * aMask a side 20) +
      (6 * aMask a side 21) +
      (6 * aMask a side 22) +
      (6 * aMask a side 23) +
      (4 * aMask a side 24) +
      (4 * aMask a side 25) +
      (4 * aMask a side 26) +
      (4 * aMask a side 27) +
      ((-1) * aMask a side 28) +
      ((-1) * aMask a side 29) +
      ((-1) * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_28_0,
      maskKrawtchoukCoeff_28_1,
      maskKrawtchoukCoeff_28_2,
      maskKrawtchoukCoeff_28_3,
      maskKrawtchoukCoeff_28_4,
      maskKrawtchoukCoeff_28_5,
      maskKrawtchoukCoeff_28_6,
      maskKrawtchoukCoeff_28_7,
      maskKrawtchoukCoeff_28_8,
      maskKrawtchoukCoeff_28_9,
      maskKrawtchoukCoeff_28_10,
      maskKrawtchoukCoeff_28_11,
      maskKrawtchoukCoeff_28_12,
      maskKrawtchoukCoeff_28_13,
      maskKrawtchoukCoeff_28_14,
      maskKrawtchoukCoeff_28_15,
      maskKrawtchoukCoeff_28_16,
      maskKrawtchoukCoeff_28_17,
      maskKrawtchoukCoeff_28_18,
      maskKrawtchoukCoeff_28_19,
      maskKrawtchoukCoeff_28_20,
      maskKrawtchoukCoeff_28_21,
      maskKrawtchoukCoeff_28_22,
      maskKrawtchoukCoeff_28_23,
      maskKrawtchoukCoeff_28_24,
      maskKrawtchoukCoeff_28_25,
      maskKrawtchoukCoeff_28_26,
      maskKrawtchoukCoeff_28_27,
      maskKrawtchoukCoeff_28_28,
      maskKrawtchoukCoeff_28_29,
      maskKrawtchoukCoeff_28_30,
      maskKrawtchoukCoeff_28_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 29. -/
theorem multiaxisEnergy_aMask_row_29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 29) =
      (240 * aMask a side 0) +
      ((-240) * aMask a side 1) +
      (240 * aMask a side 2) +
      ((-240) * aMask a side 3) +
      ((-60) * aMask a side 4) +
      (60 * aMask a side 5) +
      ((-60) * aMask a side 6) +
      (60 * aMask a side 7) +
      ((-40) * aMask a side 8) +
      (40 * aMask a side 9) +
      ((-40) * aMask a side 10) +
      (40 * aMask a side 11) +
      (10 * aMask a side 12) +
      ((-10) * aMask a side 13) +
      (10 * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-24) * aMask a side 16) +
      (24 * aMask a side 17) +
      ((-24) * aMask a side 18) +
      (24 * aMask a side 19) +
      (6 * aMask a side 20) +
      ((-6) * aMask a side 21) +
      (6 * aMask a side 22) +
      ((-6) * aMask a side 23) +
      (4 * aMask a side 24) +
      ((-4) * aMask a side 25) +
      (4 * aMask a side 26) +
      ((-4) * aMask a side 27) +
      ((-1) * aMask a side 28) +
      (1 * aMask a side 29) +
      ((-1) * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_29_0,
      maskKrawtchoukCoeff_29_1,
      maskKrawtchoukCoeff_29_2,
      maskKrawtchoukCoeff_29_3,
      maskKrawtchoukCoeff_29_4,
      maskKrawtchoukCoeff_29_5,
      maskKrawtchoukCoeff_29_6,
      maskKrawtchoukCoeff_29_7,
      maskKrawtchoukCoeff_29_8,
      maskKrawtchoukCoeff_29_9,
      maskKrawtchoukCoeff_29_10,
      maskKrawtchoukCoeff_29_11,
      maskKrawtchoukCoeff_29_12,
      maskKrawtchoukCoeff_29_13,
      maskKrawtchoukCoeff_29_14,
      maskKrawtchoukCoeff_29_15,
      maskKrawtchoukCoeff_29_16,
      maskKrawtchoukCoeff_29_17,
      maskKrawtchoukCoeff_29_18,
      maskKrawtchoukCoeff_29_19,
      maskKrawtchoukCoeff_29_20,
      maskKrawtchoukCoeff_29_21,
      maskKrawtchoukCoeff_29_22,
      maskKrawtchoukCoeff_29_23,
      maskKrawtchoukCoeff_29_24,
      maskKrawtchoukCoeff_29_25,
      maskKrawtchoukCoeff_29_26,
      maskKrawtchoukCoeff_29_27,
      maskKrawtchoukCoeff_29_28,
      maskKrawtchoukCoeff_29_29,
      maskKrawtchoukCoeff_29_30,
      maskKrawtchoukCoeff_29_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 30. -/
theorem multiaxisEnergy_aMask_row_30
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 30) =
      (480 * aMask a side 0) +
      (480 * aMask a side 1) +
      ((-240) * aMask a side 2) +
      ((-240) * aMask a side 3) +
      ((-120) * aMask a side 4) +
      ((-120) * aMask a side 5) +
      (60 * aMask a side 6) +
      (60 * aMask a side 7) +
      ((-80) * aMask a side 8) +
      ((-80) * aMask a side 9) +
      (40 * aMask a side 10) +
      (40 * aMask a side 11) +
      (20 * aMask a side 12) +
      (20 * aMask a side 13) +
      ((-10) * aMask a side 14) +
      ((-10) * aMask a side 15) +
      ((-48) * aMask a side 16) +
      ((-48) * aMask a side 17) +
      (24 * aMask a side 18) +
      (24 * aMask a side 19) +
      (12 * aMask a side 20) +
      (12 * aMask a side 21) +
      ((-6) * aMask a side 22) +
      ((-6) * aMask a side 23) +
      (8 * aMask a side 24) +
      (8 * aMask a side 25) +
      ((-4) * aMask a side 26) +
      ((-4) * aMask a side 27) +
      ((-2) * aMask a side 28) +
      ((-2) * aMask a side 29) +
      (1 * aMask a side 30) +
      (1 * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_30_0,
      maskKrawtchoukCoeff_30_1,
      maskKrawtchoukCoeff_30_2,
      maskKrawtchoukCoeff_30_3,
      maskKrawtchoukCoeff_30_4,
      maskKrawtchoukCoeff_30_5,
      maskKrawtchoukCoeff_30_6,
      maskKrawtchoukCoeff_30_7,
      maskKrawtchoukCoeff_30_8,
      maskKrawtchoukCoeff_30_9,
      maskKrawtchoukCoeff_30_10,
      maskKrawtchoukCoeff_30_11,
      maskKrawtchoukCoeff_30_12,
      maskKrawtchoukCoeff_30_13,
      maskKrawtchoukCoeff_30_14,
      maskKrawtchoukCoeff_30_15,
      maskKrawtchoukCoeff_30_16,
      maskKrawtchoukCoeff_30_17,
      maskKrawtchoukCoeff_30_18,
      maskKrawtchoukCoeff_30_19,
      maskKrawtchoukCoeff_30_20,
      maskKrawtchoukCoeff_30_21,
      maskKrawtchoukCoeff_30_22,
      maskKrawtchoukCoeff_30_23,
      maskKrawtchoukCoeff_30_24,
      maskKrawtchoukCoeff_30_25,
      maskKrawtchoukCoeff_30_26,
      maskKrawtchoukCoeff_30_27,
      maskKrawtchoukCoeff_30_28,
      maskKrawtchoukCoeff_30_29,
      maskKrawtchoukCoeff_30_30,
      maskKrawtchoukCoeff_30_31]
  norm_num [aMask]

/-- Fully evaluated Krawtchouk row 31. -/
theorem multiaxisEnergy_aMask_row_31
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisEnergy a side (axisSupportOfMask 31) =
      (480 * aMask a side 0) +
      ((-480) * aMask a side 1) +
      ((-240) * aMask a side 2) +
      (240 * aMask a side 3) +
      ((-120) * aMask a side 4) +
      (120 * aMask a side 5) +
      (60 * aMask a side 6) +
      ((-60) * aMask a side 7) +
      ((-80) * aMask a side 8) +
      (80 * aMask a side 9) +
      (40 * aMask a side 10) +
      ((-40) * aMask a side 11) +
      (20 * aMask a side 12) +
      ((-20) * aMask a side 13) +
      ((-10) * aMask a side 14) +
      (10 * aMask a side 15) +
      ((-48) * aMask a side 16) +
      (48 * aMask a side 17) +
      (24 * aMask a side 18) +
      ((-24) * aMask a side 19) +
      (12 * aMask a side 20) +
      ((-12) * aMask a side 21) +
      ((-6) * aMask a side 22) +
      (6 * aMask a side 23) +
      (8 * aMask a side 24) +
      ((-8) * aMask a side 25) +
      ((-4) * aMask a side 26) +
      (4 * aMask a side 27) +
      ((-2) * aMask a side 28) +
      (2 * aMask a side 29) +
      (1 * aMask a side 30) +
      ((-1) * aMask a side 31) := by
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit]
  simp only [aMask, krawtchoukCoeff_axisSupportOfMask,
      maskKrawtchoukCoeff_31_0,
      maskKrawtchoukCoeff_31_1,
      maskKrawtchoukCoeff_31_2,
      maskKrawtchoukCoeff_31_3,
      maskKrawtchoukCoeff_31_4,
      maskKrawtchoukCoeff_31_5,
      maskKrawtchoukCoeff_31_6,
      maskKrawtchoukCoeff_31_7,
      maskKrawtchoukCoeff_31_8,
      maskKrawtchoukCoeff_31_9,
      maskKrawtchoukCoeff_31_10,
      maskKrawtchoukCoeff_31_11,
      maskKrawtchoukCoeff_31_12,
      maskKrawtchoukCoeff_31_13,
      maskKrawtchoukCoeff_31_14,
      maskKrawtchoukCoeff_31_15,
      maskKrawtchoukCoeff_31_16,
      maskKrawtchoukCoeff_31_17,
      maskKrawtchoukCoeff_31_18,
      maskKrawtchoukCoeff_31_19,
      maskKrawtchoukCoeff_31_20,
      maskKrawtchoukCoeff_31_21,
      maskKrawtchoukCoeff_31_22,
      maskKrawtchoukCoeff_31_23,
      maskKrawtchoukCoeff_31_24,
      maskKrawtchoukCoeff_31_25,
      maskKrawtchoukCoeff_31_26,
      maskKrawtchoukCoeff_31_27,
      maskKrawtchoukCoeff_31_28,
      maskKrawtchoukCoeff_31_29,
      maskKrawtchoukCoeff_31_30,
      maskKrawtchoukCoeff_31_31]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 0. -/
theorem multiaxisProjectionCollision_aMask_row_0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 0) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 6 +
      aMask a side 7 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 10 +
      aMask a side 11 +
      aMask a side 12 +
      aMask a side 13 +
      aMask a side 14 +
      aMask a side 15 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 18 +
      aMask a side 19 +
      aMask a side 20 +
      aMask a side 21 +
      aMask a side 22 +
      aMask a side 23 +
      aMask a side 24 +
      aMask a side 25 +
      aMask a side 26 +
      aMask a side 27 +
      aMask a side 28 +
      aMask a side 29 +
      aMask a side 30 +
      aMask a side 31 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 7) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 11) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 13) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 14) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 15) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 19) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 21) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 22) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 23) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 25) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 26) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 27) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 28) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 29) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 30) (axisSupportOfMask 0) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 31) (axisSupportOfMask 0) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 1. -/
theorem multiaxisProjectionCollision_aMask_row_1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 1) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 4 +
      aMask a side 6 +
      aMask a side 8 +
      aMask a side 10 +
      aMask a side 12 +
      aMask a side 14 +
      aMask a side 16 +
      aMask a side 18 +
      aMask a side 20 +
      aMask a side 22 +
      aMask a side 24 +
      aMask a side 26 +
      aMask a side 28 +
      aMask a side 30 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 14) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 22) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 26) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 28) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 1) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 30) (axisSupportOfMask 1) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 1) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 2. -/
theorem multiaxisProjectionCollision_aMask_row_2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 2) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 12 +
      aMask a side 13 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 20 +
      aMask a side 21 +
      aMask a side 24 +
      aMask a side 25 +
      aMask a side 28 +
      aMask a side 29 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 13) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 21) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 25) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 28) (axisSupportOfMask 2) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 29) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 2) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 2) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 3. -/
theorem multiaxisProjectionCollision_aMask_row_3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 3) =
      aMask a side 0 +
      aMask a side 4 +
      aMask a side 8 +
      aMask a side 12 +
      aMask a side 16 +
      aMask a side 20 +
      aMask a side 24 +
      aMask a side 28 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 3) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 28) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 3) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 3) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 4. -/
theorem multiaxisProjectionCollision_aMask_row_4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 4) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 10 +
      aMask a side 11 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 18 +
      aMask a side 19 +
      aMask a side 24 +
      aMask a side 25 +
      aMask a side 26 +
      aMask a side 27 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 11) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 19) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 25) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 26) (axisSupportOfMask 4) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 27) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 4) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 4) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 5. -/
theorem multiaxisProjectionCollision_aMask_row_5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 5) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 8 +
      aMask a side 10 +
      aMask a side 16 +
      aMask a side 18 +
      aMask a side 24 +
      aMask a side 26 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 5) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 26) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 5) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 5) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 6. -/
theorem multiaxisProjectionCollision_aMask_row_6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 6) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 24 +
      aMask a side 25 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 6) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 25) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 6) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 6) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 7. -/
theorem multiaxisProjectionCollision_aMask_row_7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 7) =
      aMask a side 0 +
      aMask a side 8 +
      aMask a side 16 +
      aMask a side 24 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 7) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 7) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 7) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 24) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 7) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 7) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 8. -/
theorem multiaxisProjectionCollision_aMask_row_8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 8) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 6 +
      aMask a side 7 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 18 +
      aMask a side 19 +
      aMask a side 20 +
      aMask a side 21 +
      aMask a side 22 +
      aMask a side 23 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 7) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 19) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 21) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 22) (axisSupportOfMask 8) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 23) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 8) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 8) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 9. -/
theorem multiaxisProjectionCollision_aMask_row_9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 9) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 4 +
      aMask a side 6 +
      aMask a side 16 +
      aMask a side 18 +
      aMask a side 20 +
      aMask a side 22 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 9) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 22) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 9) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 9) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 10. -/
theorem multiaxisProjectionCollision_aMask_row_10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 10) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 20 +
      aMask a side 21 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 10) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 21) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 10) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 10) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 11. -/
theorem multiaxisProjectionCollision_aMask_row_11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 11) =
      aMask a side 0 +
      aMask a side 4 +
      aMask a side 16 +
      aMask a side 20 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 11) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 11) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 11) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 20) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 11) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 11) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 12. -/
theorem multiaxisProjectionCollision_aMask_row_12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 12) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 16 +
      aMask a side 17 +
      aMask a side 18 +
      aMask a side 19 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 12) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 19) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 12) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 12) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 13. -/
theorem multiaxisProjectionCollision_aMask_row_13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 13) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 16 +
      aMask a side 18 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 13) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 13) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 13) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 18) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 13) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 13) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 14. -/
theorem multiaxisProjectionCollision_aMask_row_14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 14) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 16 +
      aMask a side 17 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 14) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 14) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 14) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 17) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 14) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 14) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 15. -/
theorem multiaxisProjectionCollision_aMask_row_15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 15) =
      aMask a side 0 +
      aMask a side 16 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 15) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 16) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 15) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 15) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 16. -/
theorem multiaxisProjectionCollision_aMask_row_16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 16) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 6 +
      aMask a side 7 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 10 +
      aMask a side 11 +
      aMask a side 12 +
      aMask a side 13 +
      aMask a side 14 +
      aMask a side 15 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 7) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 11) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 13) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 14) (axisSupportOfMask 16) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 15) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 16) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 16) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 17. -/
theorem multiaxisProjectionCollision_aMask_row_17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 17) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 4 +
      aMask a side 6 +
      aMask a side 8 +
      aMask a side 10 +
      aMask a side 12 +
      aMask a side 14 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 17) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 14) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 17) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 17) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 18. -/
theorem multiaxisProjectionCollision_aMask_row_18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 18) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 12 +
      aMask a side 13 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 18) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 13) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 18) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 18) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 19. -/
theorem multiaxisProjectionCollision_aMask_row_19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 19) =
      aMask a side 0 +
      aMask a side 4 +
      aMask a side 8 +
      aMask a side 12 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 19) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 19) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 19) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 12) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 19) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 19) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 20. -/
theorem multiaxisProjectionCollision_aMask_row_20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 20) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 8 +
      aMask a side 9 +
      aMask a side 10 +
      aMask a side 11 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 20) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 11) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 20) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 20) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 21. -/
theorem multiaxisProjectionCollision_aMask_row_21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 21) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 8 +
      aMask a side 10 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 21) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 21) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 21) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 10) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 21) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 21) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 22. -/
theorem multiaxisProjectionCollision_aMask_row_22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 22) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 8 +
      aMask a side 9 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 22) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 22) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 22) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 9) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 22) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 22) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 23. -/
theorem multiaxisProjectionCollision_aMask_row_23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 23) =
      aMask a side 0 +
      aMask a side 8 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 23) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 8) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 23) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 23) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 24. -/
theorem multiaxisProjectionCollision_aMask_row_24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 24) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 +
      aMask a side 4 +
      aMask a side 5 +
      aMask a side 6 +
      aMask a side 7 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 24) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 7) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 24) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 24) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 25. -/
theorem multiaxisProjectionCollision_aMask_row_25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 25) =
      aMask a side 0 +
      aMask a side 2 +
      aMask a side 4 +
      aMask a side 6 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 25) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 25) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 25) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 6) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 25) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 25) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 26. -/
theorem multiaxisProjectionCollision_aMask_row_26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 26) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 4 +
      aMask a side 5 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 26) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 26) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 26) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 5) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 26) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 26) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 27. -/
theorem multiaxisProjectionCollision_aMask_row_27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 27) =
      aMask a side 0 +
      aMask a side 4 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 27) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 4) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 27) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 27) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 28. -/
theorem multiaxisProjectionCollision_aMask_row_28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 28) =
      aMask a side 0 +
      aMask a side 1 +
      aMask a side 2 +
      aMask a side 3 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 28) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 28) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 28) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 3) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 28) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 28) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 29. -/
theorem multiaxisProjectionCollision_aMask_row_29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 29) =
      aMask a side 0 +
      aMask a side 2 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 29) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 2) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 29) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 29) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 30. -/
theorem multiaxisProjectionCollision_aMask_row_30
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 30) =
      aMask a side 0 +
      aMask a side 1 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 30) from by decide),
      if_pos (show Disjoint (axisSupportOfMask 1) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 30) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 30) from by decide)]
  norm_num [aMask]

/-- Fully evaluated projection-collision row 31. -/
theorem multiaxisProjectionCollision_aMask_row_31
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) :
    multiaxisProjectionCollision a side (axisSupportOfMask 31) =
      aMask a side 0 := by
  rw [multiaxisProjectionCollision, sum_axisSupportOfMask_explicit]
  simp only [
      if_pos (show Disjoint (axisSupportOfMask 0) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 1) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 2) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 3) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 4) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 5) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 6) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 7) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 8) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 9) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 10) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 11) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 12) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 13) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 14) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 15) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 16) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 17) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 18) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 19) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 20) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 21) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 22) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 23) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 24) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 25) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 26) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 27) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 28) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 29) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 30) (axisSupportOfMask 31) from by decide),
      if_neg (show ¬ Disjoint (axisSupportOfMask 31) (axisSupportOfMask 31) from by decide)]
  norm_num [aMask]

end Fuglede
