import Fuglede.MultiaxisCertificateBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # Shared normalizations for multiaxis arithmetic certificates

This generated module is independent of the cardinality and SMT core.
It is compiled once and reused by every typed certificate adapter.
-/

namespace Fuglede

/-- Bit-mask `m` interpreted as a subset of the five CRT axes. -/
def axisSupportOfMask (mask : Nat) : AxisSupport2310 :=
  Finset.univ.filter fun i : Fin 5 => mask.testBit i.val

/-- Closed support rows used by all generated adapters. -/
@[simp] theorem axisSupportOfMask_0 :
    axisSupportOfMask 0 = (∅ : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_1 :
    axisSupportOfMask 1 = ({0} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_2 :
    axisSupportOfMask 2 = ({1} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_3 :
    axisSupportOfMask 3 = ({0, 1} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_4 :
    axisSupportOfMask 4 = ({2} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_5 :
    axisSupportOfMask 5 = ({0, 2} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_6 :
    axisSupportOfMask 6 = ({1, 2} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_7 :
    axisSupportOfMask 7 = ({0, 1, 2} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_8 :
    axisSupportOfMask 8 = ({3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_9 :
    axisSupportOfMask 9 = ({0, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_10 :
    axisSupportOfMask 10 = ({1, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_11 :
    axisSupportOfMask 11 = ({0, 1, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_12 :
    axisSupportOfMask 12 = ({2, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_13 :
    axisSupportOfMask 13 = ({0, 2, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_14 :
    axisSupportOfMask 14 = ({1, 2, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_15 :
    axisSupportOfMask 15 = ({0, 1, 2, 3} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_16 :
    axisSupportOfMask 16 = ({4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_17 :
    axisSupportOfMask 17 = ({0, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_18 :
    axisSupportOfMask 18 = ({1, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_19 :
    axisSupportOfMask 19 = ({0, 1, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_20 :
    axisSupportOfMask 20 = ({2, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_21 :
    axisSupportOfMask 21 = ({0, 2, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_22 :
    axisSupportOfMask 22 = ({1, 2, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_23 :
    axisSupportOfMask 23 = ({0, 1, 2, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_24 :
    axisSupportOfMask 24 = ({3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_25 :
    axisSupportOfMask 25 = ({0, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_26 :
    axisSupportOfMask 26 = ({1, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_27 :
    axisSupportOfMask 27 = ({0, 1, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_28 :
    axisSupportOfMask 28 = ({2, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_29 :
    axisSupportOfMask 29 = ({0, 2, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_30 :
    axisSupportOfMask 30 = ({1, 2, 3, 4} : AxisSupport2310) := by
  decide

@[simp] theorem axisSupportOfMask_31 :
    axisSupportOfMask 31 = ({0, 1, 2, 3, 4} : AxisSupport2310) := by
  decide

/-- The five-factor coefficient table before concrete evaluation. -/
def maskKrawtchoukCoeff (D T : Nat) : Int :=
  ∏ i : Fin 5,
    if D.testBit i.val then
      if T.testBit i.val then (-1 : Int)
      else (crt2310Modulus i : Int) - 1
    else 1

/-- Every concrete Krawtchouk coefficient reduces to the shared table. -/
theorem krawtchoukCoeff_axisSupportOfMask (D T : Nat) :
    krawtchoukCoeff (axisSupportOfMask D) (axisSupportOfMask T) =
      maskKrawtchoukCoeff D T := by
  rw [krawtchoukCoeff_eq_prod_local]
  simp [axisSupportOfMask, maskKrawtchoukCoeff, Finset.prod_filter]

/-- All 32×32 closed table entries, shared across instance adapters. -/
theorem maskKrawtchoukCoeff_0_0 :
    maskKrawtchoukCoeff 0 0 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_1 :
    maskKrawtchoukCoeff 0 1 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_2 :
    maskKrawtchoukCoeff 0 2 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_3 :
    maskKrawtchoukCoeff 0 3 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_4 :
    maskKrawtchoukCoeff 0 4 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_5 :
    maskKrawtchoukCoeff 0 5 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_6 :
    maskKrawtchoukCoeff 0 6 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_7 :
    maskKrawtchoukCoeff 0 7 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_8 :
    maskKrawtchoukCoeff 0 8 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_9 :
    maskKrawtchoukCoeff 0 9 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_10 :
    maskKrawtchoukCoeff 0 10 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_11 :
    maskKrawtchoukCoeff 0 11 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_12 :
    maskKrawtchoukCoeff 0 12 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_13 :
    maskKrawtchoukCoeff 0 13 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_14 :
    maskKrawtchoukCoeff 0 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_15 :
    maskKrawtchoukCoeff 0 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_16 :
    maskKrawtchoukCoeff 0 16 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_17 :
    maskKrawtchoukCoeff 0 17 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_18 :
    maskKrawtchoukCoeff 0 18 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_19 :
    maskKrawtchoukCoeff 0 19 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_20 :
    maskKrawtchoukCoeff 0 20 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_21 :
    maskKrawtchoukCoeff 0 21 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_22 :
    maskKrawtchoukCoeff 0 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_23 :
    maskKrawtchoukCoeff 0 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_24 :
    maskKrawtchoukCoeff 0 24 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_25 :
    maskKrawtchoukCoeff 0 25 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_26 :
    maskKrawtchoukCoeff 0 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_27 :
    maskKrawtchoukCoeff 0 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_28 :
    maskKrawtchoukCoeff 0 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_29 :
    maskKrawtchoukCoeff 0 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_30 :
    maskKrawtchoukCoeff 0 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_0_31 :
    maskKrawtchoukCoeff 0 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_0 :
    maskKrawtchoukCoeff 1 0 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_1 :
    maskKrawtchoukCoeff 1 1 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_2 :
    maskKrawtchoukCoeff 1 2 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_3 :
    maskKrawtchoukCoeff 1 3 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_4 :
    maskKrawtchoukCoeff 1 4 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_5 :
    maskKrawtchoukCoeff 1 5 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_6 :
    maskKrawtchoukCoeff 1 6 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_7 :
    maskKrawtchoukCoeff 1 7 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_8 :
    maskKrawtchoukCoeff 1 8 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_9 :
    maskKrawtchoukCoeff 1 9 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_10 :
    maskKrawtchoukCoeff 1 10 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_11 :
    maskKrawtchoukCoeff 1 11 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_12 :
    maskKrawtchoukCoeff 1 12 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_13 :
    maskKrawtchoukCoeff 1 13 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_14 :
    maskKrawtchoukCoeff 1 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_15 :
    maskKrawtchoukCoeff 1 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_16 :
    maskKrawtchoukCoeff 1 16 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_17 :
    maskKrawtchoukCoeff 1 17 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_18 :
    maskKrawtchoukCoeff 1 18 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_19 :
    maskKrawtchoukCoeff 1 19 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_20 :
    maskKrawtchoukCoeff 1 20 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_21 :
    maskKrawtchoukCoeff 1 21 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_22 :
    maskKrawtchoukCoeff 1 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_23 :
    maskKrawtchoukCoeff 1 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_24 :
    maskKrawtchoukCoeff 1 24 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_25 :
    maskKrawtchoukCoeff 1 25 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_26 :
    maskKrawtchoukCoeff 1 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_27 :
    maskKrawtchoukCoeff 1 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_28 :
    maskKrawtchoukCoeff 1 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_29 :
    maskKrawtchoukCoeff 1 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_1_30 :
    maskKrawtchoukCoeff 1 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_1_31 :
    maskKrawtchoukCoeff 1 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_0 :
    maskKrawtchoukCoeff 2 0 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_1 :
    maskKrawtchoukCoeff 2 1 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_2 :
    maskKrawtchoukCoeff 2 2 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_3 :
    maskKrawtchoukCoeff 2 3 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_4 :
    maskKrawtchoukCoeff 2 4 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_5 :
    maskKrawtchoukCoeff 2 5 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_6 :
    maskKrawtchoukCoeff 2 6 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_7 :
    maskKrawtchoukCoeff 2 7 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_8 :
    maskKrawtchoukCoeff 2 8 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_9 :
    maskKrawtchoukCoeff 2 9 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_10 :
    maskKrawtchoukCoeff 2 10 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_11 :
    maskKrawtchoukCoeff 2 11 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_12 :
    maskKrawtchoukCoeff 2 12 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_13 :
    maskKrawtchoukCoeff 2 13 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_14 :
    maskKrawtchoukCoeff 2 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_15 :
    maskKrawtchoukCoeff 2 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_16 :
    maskKrawtchoukCoeff 2 16 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_17 :
    maskKrawtchoukCoeff 2 17 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_18 :
    maskKrawtchoukCoeff 2 18 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_19 :
    maskKrawtchoukCoeff 2 19 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_20 :
    maskKrawtchoukCoeff 2 20 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_21 :
    maskKrawtchoukCoeff 2 21 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_22 :
    maskKrawtchoukCoeff 2 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_23 :
    maskKrawtchoukCoeff 2 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_24 :
    maskKrawtchoukCoeff 2 24 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_25 :
    maskKrawtchoukCoeff 2 25 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_26 :
    maskKrawtchoukCoeff 2 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_27 :
    maskKrawtchoukCoeff 2 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_28 :
    maskKrawtchoukCoeff 2 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_29 :
    maskKrawtchoukCoeff 2 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_2_30 :
    maskKrawtchoukCoeff 2 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_2_31 :
    maskKrawtchoukCoeff 2 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_0 :
    maskKrawtchoukCoeff 3 0 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_1 :
    maskKrawtchoukCoeff 3 1 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_2 :
    maskKrawtchoukCoeff 3 2 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_3 :
    maskKrawtchoukCoeff 3 3 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_4 :
    maskKrawtchoukCoeff 3 4 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_5 :
    maskKrawtchoukCoeff 3 5 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_6 :
    maskKrawtchoukCoeff 3 6 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_7 :
    maskKrawtchoukCoeff 3 7 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_8 :
    maskKrawtchoukCoeff 3 8 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_9 :
    maskKrawtchoukCoeff 3 9 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_10 :
    maskKrawtchoukCoeff 3 10 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_11 :
    maskKrawtchoukCoeff 3 11 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_12 :
    maskKrawtchoukCoeff 3 12 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_13 :
    maskKrawtchoukCoeff 3 13 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_14 :
    maskKrawtchoukCoeff 3 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_15 :
    maskKrawtchoukCoeff 3 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_16 :
    maskKrawtchoukCoeff 3 16 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_17 :
    maskKrawtchoukCoeff 3 17 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_18 :
    maskKrawtchoukCoeff 3 18 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_19 :
    maskKrawtchoukCoeff 3 19 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_20 :
    maskKrawtchoukCoeff 3 20 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_21 :
    maskKrawtchoukCoeff 3 21 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_22 :
    maskKrawtchoukCoeff 3 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_23 :
    maskKrawtchoukCoeff 3 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_24 :
    maskKrawtchoukCoeff 3 24 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_25 :
    maskKrawtchoukCoeff 3 25 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_26 :
    maskKrawtchoukCoeff 3 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_27 :
    maskKrawtchoukCoeff 3 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_3_28 :
    maskKrawtchoukCoeff 3 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_3_29 :
    maskKrawtchoukCoeff 3 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_3_30 :
    maskKrawtchoukCoeff 3 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_3_31 :
    maskKrawtchoukCoeff 3 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_4_0 :
    maskKrawtchoukCoeff 4 0 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_1 :
    maskKrawtchoukCoeff 4 1 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_2 :
    maskKrawtchoukCoeff 4 2 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_3 :
    maskKrawtchoukCoeff 4 3 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_4 :
    maskKrawtchoukCoeff 4 4 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_5 :
    maskKrawtchoukCoeff 4 5 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_6 :
    maskKrawtchoukCoeff 4 6 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_7 :
    maskKrawtchoukCoeff 4 7 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_8 :
    maskKrawtchoukCoeff 4 8 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_9 :
    maskKrawtchoukCoeff 4 9 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_10 :
    maskKrawtchoukCoeff 4 10 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_11 :
    maskKrawtchoukCoeff 4 11 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_12 :
    maskKrawtchoukCoeff 4 12 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_13 :
    maskKrawtchoukCoeff 4 13 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_14 :
    maskKrawtchoukCoeff 4 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_15 :
    maskKrawtchoukCoeff 4 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_16 :
    maskKrawtchoukCoeff 4 16 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_17 :
    maskKrawtchoukCoeff 4 17 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_18 :
    maskKrawtchoukCoeff 4 18 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_19 :
    maskKrawtchoukCoeff 4 19 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_20 :
    maskKrawtchoukCoeff 4 20 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_21 :
    maskKrawtchoukCoeff 4 21 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_22 :
    maskKrawtchoukCoeff 4 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_23 :
    maskKrawtchoukCoeff 4 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_24 :
    maskKrawtchoukCoeff 4 24 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_25 :
    maskKrawtchoukCoeff 4 25 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_26 :
    maskKrawtchoukCoeff 4 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_27 :
    maskKrawtchoukCoeff 4 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_4_28 :
    maskKrawtchoukCoeff 4 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_29 :
    maskKrawtchoukCoeff 4 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_30 :
    maskKrawtchoukCoeff 4 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_4_31 :
    maskKrawtchoukCoeff 4 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_0 :
    maskKrawtchoukCoeff 5 0 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_1 :
    maskKrawtchoukCoeff 5 1 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_2 :
    maskKrawtchoukCoeff 5 2 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_3 :
    maskKrawtchoukCoeff 5 3 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_4 :
    maskKrawtchoukCoeff 5 4 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_5 :
    maskKrawtchoukCoeff 5 5 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_6 :
    maskKrawtchoukCoeff 5 6 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_7 :
    maskKrawtchoukCoeff 5 7 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_8 :
    maskKrawtchoukCoeff 5 8 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_9 :
    maskKrawtchoukCoeff 5 9 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_10 :
    maskKrawtchoukCoeff 5 10 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_11 :
    maskKrawtchoukCoeff 5 11 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_12 :
    maskKrawtchoukCoeff 5 12 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_13 :
    maskKrawtchoukCoeff 5 13 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_14 :
    maskKrawtchoukCoeff 5 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_15 :
    maskKrawtchoukCoeff 5 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_16 :
    maskKrawtchoukCoeff 5 16 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_17 :
    maskKrawtchoukCoeff 5 17 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_18 :
    maskKrawtchoukCoeff 5 18 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_19 :
    maskKrawtchoukCoeff 5 19 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_20 :
    maskKrawtchoukCoeff 5 20 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_21 :
    maskKrawtchoukCoeff 5 21 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_22 :
    maskKrawtchoukCoeff 5 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_23 :
    maskKrawtchoukCoeff 5 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_24 :
    maskKrawtchoukCoeff 5 24 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_25 :
    maskKrawtchoukCoeff 5 25 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_26 :
    maskKrawtchoukCoeff 5 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_5_27 :
    maskKrawtchoukCoeff 5 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_5_28 :
    maskKrawtchoukCoeff 5 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_29 :
    maskKrawtchoukCoeff 5 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_5_30 :
    maskKrawtchoukCoeff 5 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_5_31 :
    maskKrawtchoukCoeff 5 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_0 :
    maskKrawtchoukCoeff 6 0 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_1 :
    maskKrawtchoukCoeff 6 1 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_2 :
    maskKrawtchoukCoeff 6 2 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_3 :
    maskKrawtchoukCoeff 6 3 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_4 :
    maskKrawtchoukCoeff 6 4 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_5 :
    maskKrawtchoukCoeff 6 5 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_6 :
    maskKrawtchoukCoeff 6 6 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_7 :
    maskKrawtchoukCoeff 6 7 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_8 :
    maskKrawtchoukCoeff 6 8 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_9 :
    maskKrawtchoukCoeff 6 9 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_10 :
    maskKrawtchoukCoeff 6 10 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_11 :
    maskKrawtchoukCoeff 6 11 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_12 :
    maskKrawtchoukCoeff 6 12 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_13 :
    maskKrawtchoukCoeff 6 13 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_14 :
    maskKrawtchoukCoeff 6 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_15 :
    maskKrawtchoukCoeff 6 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_16 :
    maskKrawtchoukCoeff 6 16 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_17 :
    maskKrawtchoukCoeff 6 17 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_18 :
    maskKrawtchoukCoeff 6 18 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_19 :
    maskKrawtchoukCoeff 6 19 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_20 :
    maskKrawtchoukCoeff 6 20 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_21 :
    maskKrawtchoukCoeff 6 21 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_22 :
    maskKrawtchoukCoeff 6 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_23 :
    maskKrawtchoukCoeff 6 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_24 :
    maskKrawtchoukCoeff 6 24 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_25 :
    maskKrawtchoukCoeff 6 25 = 8 := by
  decide

theorem maskKrawtchoukCoeff_6_26 :
    maskKrawtchoukCoeff 6 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_27 :
    maskKrawtchoukCoeff 6 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_6_28 :
    maskKrawtchoukCoeff 6 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_29 :
    maskKrawtchoukCoeff 6 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_6_30 :
    maskKrawtchoukCoeff 6 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_6_31 :
    maskKrawtchoukCoeff 6 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_7_0 :
    maskKrawtchoukCoeff 7 0 = 8 := by
  decide

theorem maskKrawtchoukCoeff_7_1 :
    maskKrawtchoukCoeff 7 1 = -8 := by
  decide

theorem maskKrawtchoukCoeff_7_2 :
    maskKrawtchoukCoeff 7 2 = -4 := by
  decide

theorem maskKrawtchoukCoeff_7_3 :
    maskKrawtchoukCoeff 7 3 = 4 := by
  decide

theorem maskKrawtchoukCoeff_7_4 :
    maskKrawtchoukCoeff 7 4 = -2 := by
  decide

theorem maskKrawtchoukCoeff_7_5 :
    maskKrawtchoukCoeff 7 5 = 2 := by
  decide

theorem maskKrawtchoukCoeff_7_6 :
    maskKrawtchoukCoeff 7 6 = 1 := by
  decide

theorem maskKrawtchoukCoeff_7_7 :
    maskKrawtchoukCoeff 7 7 = -1 := by
  decide

theorem maskKrawtchoukCoeff_7_8 :
    maskKrawtchoukCoeff 7 8 = 8 := by
  decide

theorem maskKrawtchoukCoeff_7_9 :
    maskKrawtchoukCoeff 7 9 = -8 := by
  decide

theorem maskKrawtchoukCoeff_7_10 :
    maskKrawtchoukCoeff 7 10 = -4 := by
  decide

theorem maskKrawtchoukCoeff_7_11 :
    maskKrawtchoukCoeff 7 11 = 4 := by
  decide

theorem maskKrawtchoukCoeff_7_12 :
    maskKrawtchoukCoeff 7 12 = -2 := by
  decide

theorem maskKrawtchoukCoeff_7_13 :
    maskKrawtchoukCoeff 7 13 = 2 := by
  decide

theorem maskKrawtchoukCoeff_7_14 :
    maskKrawtchoukCoeff 7 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_7_15 :
    maskKrawtchoukCoeff 7 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_7_16 :
    maskKrawtchoukCoeff 7 16 = 8 := by
  decide

theorem maskKrawtchoukCoeff_7_17 :
    maskKrawtchoukCoeff 7 17 = -8 := by
  decide

theorem maskKrawtchoukCoeff_7_18 :
    maskKrawtchoukCoeff 7 18 = -4 := by
  decide

theorem maskKrawtchoukCoeff_7_19 :
    maskKrawtchoukCoeff 7 19 = 4 := by
  decide

theorem maskKrawtchoukCoeff_7_20 :
    maskKrawtchoukCoeff 7 20 = -2 := by
  decide

theorem maskKrawtchoukCoeff_7_21 :
    maskKrawtchoukCoeff 7 21 = 2 := by
  decide

theorem maskKrawtchoukCoeff_7_22 :
    maskKrawtchoukCoeff 7 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_7_23 :
    maskKrawtchoukCoeff 7 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_7_24 :
    maskKrawtchoukCoeff 7 24 = 8 := by
  decide

theorem maskKrawtchoukCoeff_7_25 :
    maskKrawtchoukCoeff 7 25 = -8 := by
  decide

theorem maskKrawtchoukCoeff_7_26 :
    maskKrawtchoukCoeff 7 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_7_27 :
    maskKrawtchoukCoeff 7 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_7_28 :
    maskKrawtchoukCoeff 7 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_7_29 :
    maskKrawtchoukCoeff 7 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_7_30 :
    maskKrawtchoukCoeff 7 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_7_31 :
    maskKrawtchoukCoeff 7 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_0 :
    maskKrawtchoukCoeff 8 0 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_1 :
    maskKrawtchoukCoeff 8 1 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_2 :
    maskKrawtchoukCoeff 8 2 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_3 :
    maskKrawtchoukCoeff 8 3 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_4 :
    maskKrawtchoukCoeff 8 4 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_5 :
    maskKrawtchoukCoeff 8 5 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_6 :
    maskKrawtchoukCoeff 8 6 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_7 :
    maskKrawtchoukCoeff 8 7 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_8 :
    maskKrawtchoukCoeff 8 8 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_9 :
    maskKrawtchoukCoeff 8 9 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_10 :
    maskKrawtchoukCoeff 8 10 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_11 :
    maskKrawtchoukCoeff 8 11 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_12 :
    maskKrawtchoukCoeff 8 12 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_13 :
    maskKrawtchoukCoeff 8 13 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_14 :
    maskKrawtchoukCoeff 8 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_15 :
    maskKrawtchoukCoeff 8 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_16 :
    maskKrawtchoukCoeff 8 16 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_17 :
    maskKrawtchoukCoeff 8 17 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_18 :
    maskKrawtchoukCoeff 8 18 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_19 :
    maskKrawtchoukCoeff 8 19 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_20 :
    maskKrawtchoukCoeff 8 20 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_21 :
    maskKrawtchoukCoeff 8 21 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_22 :
    maskKrawtchoukCoeff 8 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_23 :
    maskKrawtchoukCoeff 8 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_8_24 :
    maskKrawtchoukCoeff 8 24 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_25 :
    maskKrawtchoukCoeff 8 25 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_26 :
    maskKrawtchoukCoeff 8 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_27 :
    maskKrawtchoukCoeff 8 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_28 :
    maskKrawtchoukCoeff 8 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_29 :
    maskKrawtchoukCoeff 8 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_30 :
    maskKrawtchoukCoeff 8 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_8_31 :
    maskKrawtchoukCoeff 8 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_0 :
    maskKrawtchoukCoeff 9 0 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_1 :
    maskKrawtchoukCoeff 9 1 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_2 :
    maskKrawtchoukCoeff 9 2 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_3 :
    maskKrawtchoukCoeff 9 3 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_4 :
    maskKrawtchoukCoeff 9 4 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_5 :
    maskKrawtchoukCoeff 9 5 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_6 :
    maskKrawtchoukCoeff 9 6 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_7 :
    maskKrawtchoukCoeff 9 7 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_8 :
    maskKrawtchoukCoeff 9 8 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_9 :
    maskKrawtchoukCoeff 9 9 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_10 :
    maskKrawtchoukCoeff 9 10 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_11 :
    maskKrawtchoukCoeff 9 11 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_12 :
    maskKrawtchoukCoeff 9 12 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_13 :
    maskKrawtchoukCoeff 9 13 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_14 :
    maskKrawtchoukCoeff 9 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_15 :
    maskKrawtchoukCoeff 9 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_16 :
    maskKrawtchoukCoeff 9 16 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_17 :
    maskKrawtchoukCoeff 9 17 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_18 :
    maskKrawtchoukCoeff 9 18 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_19 :
    maskKrawtchoukCoeff 9 19 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_20 :
    maskKrawtchoukCoeff 9 20 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_21 :
    maskKrawtchoukCoeff 9 21 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_22 :
    maskKrawtchoukCoeff 9 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_9_23 :
    maskKrawtchoukCoeff 9 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_9_24 :
    maskKrawtchoukCoeff 9 24 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_25 :
    maskKrawtchoukCoeff 9 25 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_26 :
    maskKrawtchoukCoeff 9 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_27 :
    maskKrawtchoukCoeff 9 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_28 :
    maskKrawtchoukCoeff 9 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_29 :
    maskKrawtchoukCoeff 9 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_9_30 :
    maskKrawtchoukCoeff 9 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_9_31 :
    maskKrawtchoukCoeff 9 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_0 :
    maskKrawtchoukCoeff 10 0 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_1 :
    maskKrawtchoukCoeff 10 1 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_2 :
    maskKrawtchoukCoeff 10 2 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_3 :
    maskKrawtchoukCoeff 10 3 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_4 :
    maskKrawtchoukCoeff 10 4 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_5 :
    maskKrawtchoukCoeff 10 5 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_6 :
    maskKrawtchoukCoeff 10 6 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_7 :
    maskKrawtchoukCoeff 10 7 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_8 :
    maskKrawtchoukCoeff 10 8 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_9 :
    maskKrawtchoukCoeff 10 9 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_10 :
    maskKrawtchoukCoeff 10 10 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_11 :
    maskKrawtchoukCoeff 10 11 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_12 :
    maskKrawtchoukCoeff 10 12 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_13 :
    maskKrawtchoukCoeff 10 13 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_14 :
    maskKrawtchoukCoeff 10 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_15 :
    maskKrawtchoukCoeff 10 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_16 :
    maskKrawtchoukCoeff 10 16 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_17 :
    maskKrawtchoukCoeff 10 17 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_18 :
    maskKrawtchoukCoeff 10 18 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_19 :
    maskKrawtchoukCoeff 10 19 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_20 :
    maskKrawtchoukCoeff 10 20 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_21 :
    maskKrawtchoukCoeff 10 21 = 12 := by
  decide

theorem maskKrawtchoukCoeff_10_22 :
    maskKrawtchoukCoeff 10 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_23 :
    maskKrawtchoukCoeff 10 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_10_24 :
    maskKrawtchoukCoeff 10 24 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_25 :
    maskKrawtchoukCoeff 10 25 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_26 :
    maskKrawtchoukCoeff 10 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_27 :
    maskKrawtchoukCoeff 10 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_28 :
    maskKrawtchoukCoeff 10 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_29 :
    maskKrawtchoukCoeff 10 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_10_30 :
    maskKrawtchoukCoeff 10 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_10_31 :
    maskKrawtchoukCoeff 10 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_11_0 :
    maskKrawtchoukCoeff 11 0 = 12 := by
  decide

theorem maskKrawtchoukCoeff_11_1 :
    maskKrawtchoukCoeff 11 1 = -12 := by
  decide

theorem maskKrawtchoukCoeff_11_2 :
    maskKrawtchoukCoeff 11 2 = -6 := by
  decide

theorem maskKrawtchoukCoeff_11_3 :
    maskKrawtchoukCoeff 11 3 = 6 := by
  decide

theorem maskKrawtchoukCoeff_11_4 :
    maskKrawtchoukCoeff 11 4 = 12 := by
  decide

theorem maskKrawtchoukCoeff_11_5 :
    maskKrawtchoukCoeff 11 5 = -12 := by
  decide

theorem maskKrawtchoukCoeff_11_6 :
    maskKrawtchoukCoeff 11 6 = -6 := by
  decide

theorem maskKrawtchoukCoeff_11_7 :
    maskKrawtchoukCoeff 11 7 = 6 := by
  decide

theorem maskKrawtchoukCoeff_11_8 :
    maskKrawtchoukCoeff 11 8 = -2 := by
  decide

theorem maskKrawtchoukCoeff_11_9 :
    maskKrawtchoukCoeff 11 9 = 2 := by
  decide

theorem maskKrawtchoukCoeff_11_10 :
    maskKrawtchoukCoeff 11 10 = 1 := by
  decide

theorem maskKrawtchoukCoeff_11_11 :
    maskKrawtchoukCoeff 11 11 = -1 := by
  decide

theorem maskKrawtchoukCoeff_11_12 :
    maskKrawtchoukCoeff 11 12 = -2 := by
  decide

theorem maskKrawtchoukCoeff_11_13 :
    maskKrawtchoukCoeff 11 13 = 2 := by
  decide

theorem maskKrawtchoukCoeff_11_14 :
    maskKrawtchoukCoeff 11 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_11_15 :
    maskKrawtchoukCoeff 11 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_11_16 :
    maskKrawtchoukCoeff 11 16 = 12 := by
  decide

theorem maskKrawtchoukCoeff_11_17 :
    maskKrawtchoukCoeff 11 17 = -12 := by
  decide

theorem maskKrawtchoukCoeff_11_18 :
    maskKrawtchoukCoeff 11 18 = -6 := by
  decide

theorem maskKrawtchoukCoeff_11_19 :
    maskKrawtchoukCoeff 11 19 = 6 := by
  decide

theorem maskKrawtchoukCoeff_11_20 :
    maskKrawtchoukCoeff 11 20 = 12 := by
  decide

theorem maskKrawtchoukCoeff_11_21 :
    maskKrawtchoukCoeff 11 21 = -12 := by
  decide

theorem maskKrawtchoukCoeff_11_22 :
    maskKrawtchoukCoeff 11 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_11_23 :
    maskKrawtchoukCoeff 11 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_11_24 :
    maskKrawtchoukCoeff 11 24 = -2 := by
  decide

theorem maskKrawtchoukCoeff_11_25 :
    maskKrawtchoukCoeff 11 25 = 2 := by
  decide

theorem maskKrawtchoukCoeff_11_26 :
    maskKrawtchoukCoeff 11 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_11_27 :
    maskKrawtchoukCoeff 11 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_11_28 :
    maskKrawtchoukCoeff 11 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_11_29 :
    maskKrawtchoukCoeff 11 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_11_30 :
    maskKrawtchoukCoeff 11 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_11_31 :
    maskKrawtchoukCoeff 11 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_12_0 :
    maskKrawtchoukCoeff 12 0 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_1 :
    maskKrawtchoukCoeff 12 1 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_2 :
    maskKrawtchoukCoeff 12 2 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_3 :
    maskKrawtchoukCoeff 12 3 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_4 :
    maskKrawtchoukCoeff 12 4 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_5 :
    maskKrawtchoukCoeff 12 5 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_6 :
    maskKrawtchoukCoeff 12 6 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_7 :
    maskKrawtchoukCoeff 12 7 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_8 :
    maskKrawtchoukCoeff 12 8 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_9 :
    maskKrawtchoukCoeff 12 9 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_10 :
    maskKrawtchoukCoeff 12 10 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_11 :
    maskKrawtchoukCoeff 12 11 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_12 :
    maskKrawtchoukCoeff 12 12 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_13 :
    maskKrawtchoukCoeff 12 13 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_14 :
    maskKrawtchoukCoeff 12 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_15 :
    maskKrawtchoukCoeff 12 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_16 :
    maskKrawtchoukCoeff 12 16 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_17 :
    maskKrawtchoukCoeff 12 17 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_18 :
    maskKrawtchoukCoeff 12 18 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_19 :
    maskKrawtchoukCoeff 12 19 = 24 := by
  decide

theorem maskKrawtchoukCoeff_12_20 :
    maskKrawtchoukCoeff 12 20 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_21 :
    maskKrawtchoukCoeff 12 21 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_22 :
    maskKrawtchoukCoeff 12 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_23 :
    maskKrawtchoukCoeff 12 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_12_24 :
    maskKrawtchoukCoeff 12 24 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_25 :
    maskKrawtchoukCoeff 12 25 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_26 :
    maskKrawtchoukCoeff 12 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_27 :
    maskKrawtchoukCoeff 12 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_12_28 :
    maskKrawtchoukCoeff 12 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_29 :
    maskKrawtchoukCoeff 12 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_30 :
    maskKrawtchoukCoeff 12 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_12_31 :
    maskKrawtchoukCoeff 12 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_13_0 :
    maskKrawtchoukCoeff 13 0 = 24 := by
  decide

theorem maskKrawtchoukCoeff_13_1 :
    maskKrawtchoukCoeff 13 1 = -24 := by
  decide

theorem maskKrawtchoukCoeff_13_2 :
    maskKrawtchoukCoeff 13 2 = 24 := by
  decide

theorem maskKrawtchoukCoeff_13_3 :
    maskKrawtchoukCoeff 13 3 = -24 := by
  decide

theorem maskKrawtchoukCoeff_13_4 :
    maskKrawtchoukCoeff 13 4 = -6 := by
  decide

theorem maskKrawtchoukCoeff_13_5 :
    maskKrawtchoukCoeff 13 5 = 6 := by
  decide

theorem maskKrawtchoukCoeff_13_6 :
    maskKrawtchoukCoeff 13 6 = -6 := by
  decide

theorem maskKrawtchoukCoeff_13_7 :
    maskKrawtchoukCoeff 13 7 = 6 := by
  decide

theorem maskKrawtchoukCoeff_13_8 :
    maskKrawtchoukCoeff 13 8 = -4 := by
  decide

theorem maskKrawtchoukCoeff_13_9 :
    maskKrawtchoukCoeff 13 9 = 4 := by
  decide

theorem maskKrawtchoukCoeff_13_10 :
    maskKrawtchoukCoeff 13 10 = -4 := by
  decide

theorem maskKrawtchoukCoeff_13_11 :
    maskKrawtchoukCoeff 13 11 = 4 := by
  decide

theorem maskKrawtchoukCoeff_13_12 :
    maskKrawtchoukCoeff 13 12 = 1 := by
  decide

theorem maskKrawtchoukCoeff_13_13 :
    maskKrawtchoukCoeff 13 13 = -1 := by
  decide

theorem maskKrawtchoukCoeff_13_14 :
    maskKrawtchoukCoeff 13 14 = 1 := by
  decide

theorem maskKrawtchoukCoeff_13_15 :
    maskKrawtchoukCoeff 13 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_13_16 :
    maskKrawtchoukCoeff 13 16 = 24 := by
  decide

theorem maskKrawtchoukCoeff_13_17 :
    maskKrawtchoukCoeff 13 17 = -24 := by
  decide

theorem maskKrawtchoukCoeff_13_18 :
    maskKrawtchoukCoeff 13 18 = 24 := by
  decide

theorem maskKrawtchoukCoeff_13_19 :
    maskKrawtchoukCoeff 13 19 = -24 := by
  decide

theorem maskKrawtchoukCoeff_13_20 :
    maskKrawtchoukCoeff 13 20 = -6 := by
  decide

theorem maskKrawtchoukCoeff_13_21 :
    maskKrawtchoukCoeff 13 21 = 6 := by
  decide

theorem maskKrawtchoukCoeff_13_22 :
    maskKrawtchoukCoeff 13 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_13_23 :
    maskKrawtchoukCoeff 13 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_13_24 :
    maskKrawtchoukCoeff 13 24 = -4 := by
  decide

theorem maskKrawtchoukCoeff_13_25 :
    maskKrawtchoukCoeff 13 25 = 4 := by
  decide

theorem maskKrawtchoukCoeff_13_26 :
    maskKrawtchoukCoeff 13 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_13_27 :
    maskKrawtchoukCoeff 13 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_13_28 :
    maskKrawtchoukCoeff 13 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_13_29 :
    maskKrawtchoukCoeff 13 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_13_30 :
    maskKrawtchoukCoeff 13 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_13_31 :
    maskKrawtchoukCoeff 13 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_14_0 :
    maskKrawtchoukCoeff 14 0 = 48 := by
  decide

theorem maskKrawtchoukCoeff_14_1 :
    maskKrawtchoukCoeff 14 1 = 48 := by
  decide

theorem maskKrawtchoukCoeff_14_2 :
    maskKrawtchoukCoeff 14 2 = -24 := by
  decide

theorem maskKrawtchoukCoeff_14_3 :
    maskKrawtchoukCoeff 14 3 = -24 := by
  decide

theorem maskKrawtchoukCoeff_14_4 :
    maskKrawtchoukCoeff 14 4 = -12 := by
  decide

theorem maskKrawtchoukCoeff_14_5 :
    maskKrawtchoukCoeff 14 5 = -12 := by
  decide

theorem maskKrawtchoukCoeff_14_6 :
    maskKrawtchoukCoeff 14 6 = 6 := by
  decide

theorem maskKrawtchoukCoeff_14_7 :
    maskKrawtchoukCoeff 14 7 = 6 := by
  decide

theorem maskKrawtchoukCoeff_14_8 :
    maskKrawtchoukCoeff 14 8 = -8 := by
  decide

theorem maskKrawtchoukCoeff_14_9 :
    maskKrawtchoukCoeff 14 9 = -8 := by
  decide

theorem maskKrawtchoukCoeff_14_10 :
    maskKrawtchoukCoeff 14 10 = 4 := by
  decide

theorem maskKrawtchoukCoeff_14_11 :
    maskKrawtchoukCoeff 14 11 = 4 := by
  decide

theorem maskKrawtchoukCoeff_14_12 :
    maskKrawtchoukCoeff 14 12 = 2 := by
  decide

theorem maskKrawtchoukCoeff_14_13 :
    maskKrawtchoukCoeff 14 13 = 2 := by
  decide

theorem maskKrawtchoukCoeff_14_14 :
    maskKrawtchoukCoeff 14 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_14_15 :
    maskKrawtchoukCoeff 14 15 = -1 := by
  decide

theorem maskKrawtchoukCoeff_14_16 :
    maskKrawtchoukCoeff 14 16 = 48 := by
  decide

theorem maskKrawtchoukCoeff_14_17 :
    maskKrawtchoukCoeff 14 17 = 48 := by
  decide

theorem maskKrawtchoukCoeff_14_18 :
    maskKrawtchoukCoeff 14 18 = -24 := by
  decide

theorem maskKrawtchoukCoeff_14_19 :
    maskKrawtchoukCoeff 14 19 = -24 := by
  decide

theorem maskKrawtchoukCoeff_14_20 :
    maskKrawtchoukCoeff 14 20 = -12 := by
  decide

theorem maskKrawtchoukCoeff_14_21 :
    maskKrawtchoukCoeff 14 21 = -12 := by
  decide

theorem maskKrawtchoukCoeff_14_22 :
    maskKrawtchoukCoeff 14 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_14_23 :
    maskKrawtchoukCoeff 14 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_14_24 :
    maskKrawtchoukCoeff 14 24 = -8 := by
  decide

theorem maskKrawtchoukCoeff_14_25 :
    maskKrawtchoukCoeff 14 25 = -8 := by
  decide

theorem maskKrawtchoukCoeff_14_26 :
    maskKrawtchoukCoeff 14 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_14_27 :
    maskKrawtchoukCoeff 14 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_14_28 :
    maskKrawtchoukCoeff 14 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_14_29 :
    maskKrawtchoukCoeff 14 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_14_30 :
    maskKrawtchoukCoeff 14 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_14_31 :
    maskKrawtchoukCoeff 14 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_15_0 :
    maskKrawtchoukCoeff 15 0 = 48 := by
  decide

theorem maskKrawtchoukCoeff_15_1 :
    maskKrawtchoukCoeff 15 1 = -48 := by
  decide

theorem maskKrawtchoukCoeff_15_2 :
    maskKrawtchoukCoeff 15 2 = -24 := by
  decide

theorem maskKrawtchoukCoeff_15_3 :
    maskKrawtchoukCoeff 15 3 = 24 := by
  decide

theorem maskKrawtchoukCoeff_15_4 :
    maskKrawtchoukCoeff 15 4 = -12 := by
  decide

theorem maskKrawtchoukCoeff_15_5 :
    maskKrawtchoukCoeff 15 5 = 12 := by
  decide

theorem maskKrawtchoukCoeff_15_6 :
    maskKrawtchoukCoeff 15 6 = 6 := by
  decide

theorem maskKrawtchoukCoeff_15_7 :
    maskKrawtchoukCoeff 15 7 = -6 := by
  decide

theorem maskKrawtchoukCoeff_15_8 :
    maskKrawtchoukCoeff 15 8 = -8 := by
  decide

theorem maskKrawtchoukCoeff_15_9 :
    maskKrawtchoukCoeff 15 9 = 8 := by
  decide

theorem maskKrawtchoukCoeff_15_10 :
    maskKrawtchoukCoeff 15 10 = 4 := by
  decide

theorem maskKrawtchoukCoeff_15_11 :
    maskKrawtchoukCoeff 15 11 = -4 := by
  decide

theorem maskKrawtchoukCoeff_15_12 :
    maskKrawtchoukCoeff 15 12 = 2 := by
  decide

theorem maskKrawtchoukCoeff_15_13 :
    maskKrawtchoukCoeff 15 13 = -2 := by
  decide

theorem maskKrawtchoukCoeff_15_14 :
    maskKrawtchoukCoeff 15 14 = -1 := by
  decide

theorem maskKrawtchoukCoeff_15_15 :
    maskKrawtchoukCoeff 15 15 = 1 := by
  decide

theorem maskKrawtchoukCoeff_15_16 :
    maskKrawtchoukCoeff 15 16 = 48 := by
  decide

theorem maskKrawtchoukCoeff_15_17 :
    maskKrawtchoukCoeff 15 17 = -48 := by
  decide

theorem maskKrawtchoukCoeff_15_18 :
    maskKrawtchoukCoeff 15 18 = -24 := by
  decide

theorem maskKrawtchoukCoeff_15_19 :
    maskKrawtchoukCoeff 15 19 = 24 := by
  decide

theorem maskKrawtchoukCoeff_15_20 :
    maskKrawtchoukCoeff 15 20 = -12 := by
  decide

theorem maskKrawtchoukCoeff_15_21 :
    maskKrawtchoukCoeff 15 21 = 12 := by
  decide

theorem maskKrawtchoukCoeff_15_22 :
    maskKrawtchoukCoeff 15 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_15_23 :
    maskKrawtchoukCoeff 15 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_15_24 :
    maskKrawtchoukCoeff 15 24 = -8 := by
  decide

theorem maskKrawtchoukCoeff_15_25 :
    maskKrawtchoukCoeff 15 25 = 8 := by
  decide

theorem maskKrawtchoukCoeff_15_26 :
    maskKrawtchoukCoeff 15 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_15_27 :
    maskKrawtchoukCoeff 15 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_15_28 :
    maskKrawtchoukCoeff 15 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_15_29 :
    maskKrawtchoukCoeff 15 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_15_30 :
    maskKrawtchoukCoeff 15 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_15_31 :
    maskKrawtchoukCoeff 15 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_16_0 :
    maskKrawtchoukCoeff 16 0 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_1 :
    maskKrawtchoukCoeff 16 1 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_2 :
    maskKrawtchoukCoeff 16 2 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_3 :
    maskKrawtchoukCoeff 16 3 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_4 :
    maskKrawtchoukCoeff 16 4 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_5 :
    maskKrawtchoukCoeff 16 5 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_6 :
    maskKrawtchoukCoeff 16 6 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_7 :
    maskKrawtchoukCoeff 16 7 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_8 :
    maskKrawtchoukCoeff 16 8 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_9 :
    maskKrawtchoukCoeff 16 9 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_10 :
    maskKrawtchoukCoeff 16 10 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_11 :
    maskKrawtchoukCoeff 16 11 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_12 :
    maskKrawtchoukCoeff 16 12 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_13 :
    maskKrawtchoukCoeff 16 13 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_14 :
    maskKrawtchoukCoeff 16 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_15 :
    maskKrawtchoukCoeff 16 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_16_16 :
    maskKrawtchoukCoeff 16 16 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_17 :
    maskKrawtchoukCoeff 16 17 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_18 :
    maskKrawtchoukCoeff 16 18 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_19 :
    maskKrawtchoukCoeff 16 19 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_20 :
    maskKrawtchoukCoeff 16 20 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_21 :
    maskKrawtchoukCoeff 16 21 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_22 :
    maskKrawtchoukCoeff 16 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_23 :
    maskKrawtchoukCoeff 16 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_24 :
    maskKrawtchoukCoeff 16 24 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_25 :
    maskKrawtchoukCoeff 16 25 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_26 :
    maskKrawtchoukCoeff 16 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_27 :
    maskKrawtchoukCoeff 16 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_28 :
    maskKrawtchoukCoeff 16 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_29 :
    maskKrawtchoukCoeff 16 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_30 :
    maskKrawtchoukCoeff 16 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_16_31 :
    maskKrawtchoukCoeff 16 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_0 :
    maskKrawtchoukCoeff 17 0 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_1 :
    maskKrawtchoukCoeff 17 1 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_2 :
    maskKrawtchoukCoeff 17 2 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_3 :
    maskKrawtchoukCoeff 17 3 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_4 :
    maskKrawtchoukCoeff 17 4 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_5 :
    maskKrawtchoukCoeff 17 5 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_6 :
    maskKrawtchoukCoeff 17 6 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_7 :
    maskKrawtchoukCoeff 17 7 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_8 :
    maskKrawtchoukCoeff 17 8 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_9 :
    maskKrawtchoukCoeff 17 9 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_10 :
    maskKrawtchoukCoeff 17 10 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_11 :
    maskKrawtchoukCoeff 17 11 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_12 :
    maskKrawtchoukCoeff 17 12 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_13 :
    maskKrawtchoukCoeff 17 13 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_14 :
    maskKrawtchoukCoeff 17 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_17_15 :
    maskKrawtchoukCoeff 17 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_17_16 :
    maskKrawtchoukCoeff 17 16 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_17 :
    maskKrawtchoukCoeff 17 17 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_18 :
    maskKrawtchoukCoeff 17 18 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_19 :
    maskKrawtchoukCoeff 17 19 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_20 :
    maskKrawtchoukCoeff 17 20 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_21 :
    maskKrawtchoukCoeff 17 21 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_22 :
    maskKrawtchoukCoeff 17 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_23 :
    maskKrawtchoukCoeff 17 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_24 :
    maskKrawtchoukCoeff 17 24 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_25 :
    maskKrawtchoukCoeff 17 25 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_26 :
    maskKrawtchoukCoeff 17 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_27 :
    maskKrawtchoukCoeff 17 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_28 :
    maskKrawtchoukCoeff 17 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_29 :
    maskKrawtchoukCoeff 17 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_17_30 :
    maskKrawtchoukCoeff 17 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_17_31 :
    maskKrawtchoukCoeff 17 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_0 :
    maskKrawtchoukCoeff 18 0 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_1 :
    maskKrawtchoukCoeff 18 1 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_2 :
    maskKrawtchoukCoeff 18 2 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_3 :
    maskKrawtchoukCoeff 18 3 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_4 :
    maskKrawtchoukCoeff 18 4 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_5 :
    maskKrawtchoukCoeff 18 5 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_6 :
    maskKrawtchoukCoeff 18 6 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_7 :
    maskKrawtchoukCoeff 18 7 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_8 :
    maskKrawtchoukCoeff 18 8 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_9 :
    maskKrawtchoukCoeff 18 9 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_10 :
    maskKrawtchoukCoeff 18 10 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_11 :
    maskKrawtchoukCoeff 18 11 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_12 :
    maskKrawtchoukCoeff 18 12 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_13 :
    maskKrawtchoukCoeff 18 13 = 20 := by
  decide

theorem maskKrawtchoukCoeff_18_14 :
    maskKrawtchoukCoeff 18 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_15 :
    maskKrawtchoukCoeff 18 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_18_16 :
    maskKrawtchoukCoeff 18 16 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_17 :
    maskKrawtchoukCoeff 18 17 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_18 :
    maskKrawtchoukCoeff 18 18 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_19 :
    maskKrawtchoukCoeff 18 19 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_20 :
    maskKrawtchoukCoeff 18 20 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_21 :
    maskKrawtchoukCoeff 18 21 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_22 :
    maskKrawtchoukCoeff 18 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_23 :
    maskKrawtchoukCoeff 18 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_24 :
    maskKrawtchoukCoeff 18 24 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_25 :
    maskKrawtchoukCoeff 18 25 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_26 :
    maskKrawtchoukCoeff 18 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_27 :
    maskKrawtchoukCoeff 18 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_28 :
    maskKrawtchoukCoeff 18 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_29 :
    maskKrawtchoukCoeff 18 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_18_30 :
    maskKrawtchoukCoeff 18 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_18_31 :
    maskKrawtchoukCoeff 18 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_19_0 :
    maskKrawtchoukCoeff 19 0 = 20 := by
  decide

theorem maskKrawtchoukCoeff_19_1 :
    maskKrawtchoukCoeff 19 1 = -20 := by
  decide

theorem maskKrawtchoukCoeff_19_2 :
    maskKrawtchoukCoeff 19 2 = -10 := by
  decide

theorem maskKrawtchoukCoeff_19_3 :
    maskKrawtchoukCoeff 19 3 = 10 := by
  decide

theorem maskKrawtchoukCoeff_19_4 :
    maskKrawtchoukCoeff 19 4 = 20 := by
  decide

theorem maskKrawtchoukCoeff_19_5 :
    maskKrawtchoukCoeff 19 5 = -20 := by
  decide

theorem maskKrawtchoukCoeff_19_6 :
    maskKrawtchoukCoeff 19 6 = -10 := by
  decide

theorem maskKrawtchoukCoeff_19_7 :
    maskKrawtchoukCoeff 19 7 = 10 := by
  decide

theorem maskKrawtchoukCoeff_19_8 :
    maskKrawtchoukCoeff 19 8 = 20 := by
  decide

theorem maskKrawtchoukCoeff_19_9 :
    maskKrawtchoukCoeff 19 9 = -20 := by
  decide

theorem maskKrawtchoukCoeff_19_10 :
    maskKrawtchoukCoeff 19 10 = -10 := by
  decide

theorem maskKrawtchoukCoeff_19_11 :
    maskKrawtchoukCoeff 19 11 = 10 := by
  decide

theorem maskKrawtchoukCoeff_19_12 :
    maskKrawtchoukCoeff 19 12 = 20 := by
  decide

theorem maskKrawtchoukCoeff_19_13 :
    maskKrawtchoukCoeff 19 13 = -20 := by
  decide

theorem maskKrawtchoukCoeff_19_14 :
    maskKrawtchoukCoeff 19 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_19_15 :
    maskKrawtchoukCoeff 19 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_19_16 :
    maskKrawtchoukCoeff 19 16 = -2 := by
  decide

theorem maskKrawtchoukCoeff_19_17 :
    maskKrawtchoukCoeff 19 17 = 2 := by
  decide

theorem maskKrawtchoukCoeff_19_18 :
    maskKrawtchoukCoeff 19 18 = 1 := by
  decide

theorem maskKrawtchoukCoeff_19_19 :
    maskKrawtchoukCoeff 19 19 = -1 := by
  decide

theorem maskKrawtchoukCoeff_19_20 :
    maskKrawtchoukCoeff 19 20 = -2 := by
  decide

theorem maskKrawtchoukCoeff_19_21 :
    maskKrawtchoukCoeff 19 21 = 2 := by
  decide

theorem maskKrawtchoukCoeff_19_22 :
    maskKrawtchoukCoeff 19 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_19_23 :
    maskKrawtchoukCoeff 19 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_19_24 :
    maskKrawtchoukCoeff 19 24 = -2 := by
  decide

theorem maskKrawtchoukCoeff_19_25 :
    maskKrawtchoukCoeff 19 25 = 2 := by
  decide

theorem maskKrawtchoukCoeff_19_26 :
    maskKrawtchoukCoeff 19 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_19_27 :
    maskKrawtchoukCoeff 19 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_19_28 :
    maskKrawtchoukCoeff 19 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_19_29 :
    maskKrawtchoukCoeff 19 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_19_30 :
    maskKrawtchoukCoeff 19 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_19_31 :
    maskKrawtchoukCoeff 19 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_20_0 :
    maskKrawtchoukCoeff 20 0 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_1 :
    maskKrawtchoukCoeff 20 1 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_2 :
    maskKrawtchoukCoeff 20 2 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_3 :
    maskKrawtchoukCoeff 20 3 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_4 :
    maskKrawtchoukCoeff 20 4 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_5 :
    maskKrawtchoukCoeff 20 5 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_6 :
    maskKrawtchoukCoeff 20 6 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_7 :
    maskKrawtchoukCoeff 20 7 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_8 :
    maskKrawtchoukCoeff 20 8 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_9 :
    maskKrawtchoukCoeff 20 9 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_10 :
    maskKrawtchoukCoeff 20 10 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_11 :
    maskKrawtchoukCoeff 20 11 = 40 := by
  decide

theorem maskKrawtchoukCoeff_20_12 :
    maskKrawtchoukCoeff 20 12 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_13 :
    maskKrawtchoukCoeff 20 13 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_14 :
    maskKrawtchoukCoeff 20 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_15 :
    maskKrawtchoukCoeff 20 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_20_16 :
    maskKrawtchoukCoeff 20 16 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_17 :
    maskKrawtchoukCoeff 20 17 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_18 :
    maskKrawtchoukCoeff 20 18 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_19 :
    maskKrawtchoukCoeff 20 19 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_20 :
    maskKrawtchoukCoeff 20 20 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_21 :
    maskKrawtchoukCoeff 20 21 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_22 :
    maskKrawtchoukCoeff 20 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_23 :
    maskKrawtchoukCoeff 20 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_24 :
    maskKrawtchoukCoeff 20 24 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_25 :
    maskKrawtchoukCoeff 20 25 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_26 :
    maskKrawtchoukCoeff 20 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_27 :
    maskKrawtchoukCoeff 20 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_20_28 :
    maskKrawtchoukCoeff 20 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_29 :
    maskKrawtchoukCoeff 20 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_30 :
    maskKrawtchoukCoeff 20 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_20_31 :
    maskKrawtchoukCoeff 20 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_21_0 :
    maskKrawtchoukCoeff 21 0 = 40 := by
  decide

theorem maskKrawtchoukCoeff_21_1 :
    maskKrawtchoukCoeff 21 1 = -40 := by
  decide

theorem maskKrawtchoukCoeff_21_2 :
    maskKrawtchoukCoeff 21 2 = 40 := by
  decide

theorem maskKrawtchoukCoeff_21_3 :
    maskKrawtchoukCoeff 21 3 = -40 := by
  decide

theorem maskKrawtchoukCoeff_21_4 :
    maskKrawtchoukCoeff 21 4 = -10 := by
  decide

theorem maskKrawtchoukCoeff_21_5 :
    maskKrawtchoukCoeff 21 5 = 10 := by
  decide

theorem maskKrawtchoukCoeff_21_6 :
    maskKrawtchoukCoeff 21 6 = -10 := by
  decide

theorem maskKrawtchoukCoeff_21_7 :
    maskKrawtchoukCoeff 21 7 = 10 := by
  decide

theorem maskKrawtchoukCoeff_21_8 :
    maskKrawtchoukCoeff 21 8 = 40 := by
  decide

theorem maskKrawtchoukCoeff_21_9 :
    maskKrawtchoukCoeff 21 9 = -40 := by
  decide

theorem maskKrawtchoukCoeff_21_10 :
    maskKrawtchoukCoeff 21 10 = 40 := by
  decide

theorem maskKrawtchoukCoeff_21_11 :
    maskKrawtchoukCoeff 21 11 = -40 := by
  decide

theorem maskKrawtchoukCoeff_21_12 :
    maskKrawtchoukCoeff 21 12 = -10 := by
  decide

theorem maskKrawtchoukCoeff_21_13 :
    maskKrawtchoukCoeff 21 13 = 10 := by
  decide

theorem maskKrawtchoukCoeff_21_14 :
    maskKrawtchoukCoeff 21 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_21_15 :
    maskKrawtchoukCoeff 21 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_21_16 :
    maskKrawtchoukCoeff 21 16 = -4 := by
  decide

theorem maskKrawtchoukCoeff_21_17 :
    maskKrawtchoukCoeff 21 17 = 4 := by
  decide

theorem maskKrawtchoukCoeff_21_18 :
    maskKrawtchoukCoeff 21 18 = -4 := by
  decide

theorem maskKrawtchoukCoeff_21_19 :
    maskKrawtchoukCoeff 21 19 = 4 := by
  decide

theorem maskKrawtchoukCoeff_21_20 :
    maskKrawtchoukCoeff 21 20 = 1 := by
  decide

theorem maskKrawtchoukCoeff_21_21 :
    maskKrawtchoukCoeff 21 21 = -1 := by
  decide

theorem maskKrawtchoukCoeff_21_22 :
    maskKrawtchoukCoeff 21 22 = 1 := by
  decide

theorem maskKrawtchoukCoeff_21_23 :
    maskKrawtchoukCoeff 21 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_21_24 :
    maskKrawtchoukCoeff 21 24 = -4 := by
  decide

theorem maskKrawtchoukCoeff_21_25 :
    maskKrawtchoukCoeff 21 25 = 4 := by
  decide

theorem maskKrawtchoukCoeff_21_26 :
    maskKrawtchoukCoeff 21 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_21_27 :
    maskKrawtchoukCoeff 21 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_21_28 :
    maskKrawtchoukCoeff 21 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_21_29 :
    maskKrawtchoukCoeff 21 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_21_30 :
    maskKrawtchoukCoeff 21 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_21_31 :
    maskKrawtchoukCoeff 21 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_22_0 :
    maskKrawtchoukCoeff 22 0 = 80 := by
  decide

theorem maskKrawtchoukCoeff_22_1 :
    maskKrawtchoukCoeff 22 1 = 80 := by
  decide

theorem maskKrawtchoukCoeff_22_2 :
    maskKrawtchoukCoeff 22 2 = -40 := by
  decide

theorem maskKrawtchoukCoeff_22_3 :
    maskKrawtchoukCoeff 22 3 = -40 := by
  decide

theorem maskKrawtchoukCoeff_22_4 :
    maskKrawtchoukCoeff 22 4 = -20 := by
  decide

theorem maskKrawtchoukCoeff_22_5 :
    maskKrawtchoukCoeff 22 5 = -20 := by
  decide

theorem maskKrawtchoukCoeff_22_6 :
    maskKrawtchoukCoeff 22 6 = 10 := by
  decide

theorem maskKrawtchoukCoeff_22_7 :
    maskKrawtchoukCoeff 22 7 = 10 := by
  decide

theorem maskKrawtchoukCoeff_22_8 :
    maskKrawtchoukCoeff 22 8 = 80 := by
  decide

theorem maskKrawtchoukCoeff_22_9 :
    maskKrawtchoukCoeff 22 9 = 80 := by
  decide

theorem maskKrawtchoukCoeff_22_10 :
    maskKrawtchoukCoeff 22 10 = -40 := by
  decide

theorem maskKrawtchoukCoeff_22_11 :
    maskKrawtchoukCoeff 22 11 = -40 := by
  decide

theorem maskKrawtchoukCoeff_22_12 :
    maskKrawtchoukCoeff 22 12 = -20 := by
  decide

theorem maskKrawtchoukCoeff_22_13 :
    maskKrawtchoukCoeff 22 13 = -20 := by
  decide

theorem maskKrawtchoukCoeff_22_14 :
    maskKrawtchoukCoeff 22 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_22_15 :
    maskKrawtchoukCoeff 22 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_22_16 :
    maskKrawtchoukCoeff 22 16 = -8 := by
  decide

theorem maskKrawtchoukCoeff_22_17 :
    maskKrawtchoukCoeff 22 17 = -8 := by
  decide

theorem maskKrawtchoukCoeff_22_18 :
    maskKrawtchoukCoeff 22 18 = 4 := by
  decide

theorem maskKrawtchoukCoeff_22_19 :
    maskKrawtchoukCoeff 22 19 = 4 := by
  decide

theorem maskKrawtchoukCoeff_22_20 :
    maskKrawtchoukCoeff 22 20 = 2 := by
  decide

theorem maskKrawtchoukCoeff_22_21 :
    maskKrawtchoukCoeff 22 21 = 2 := by
  decide

theorem maskKrawtchoukCoeff_22_22 :
    maskKrawtchoukCoeff 22 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_22_23 :
    maskKrawtchoukCoeff 22 23 = -1 := by
  decide

theorem maskKrawtchoukCoeff_22_24 :
    maskKrawtchoukCoeff 22 24 = -8 := by
  decide

theorem maskKrawtchoukCoeff_22_25 :
    maskKrawtchoukCoeff 22 25 = -8 := by
  decide

theorem maskKrawtchoukCoeff_22_26 :
    maskKrawtchoukCoeff 22 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_22_27 :
    maskKrawtchoukCoeff 22 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_22_28 :
    maskKrawtchoukCoeff 22 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_22_29 :
    maskKrawtchoukCoeff 22 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_22_30 :
    maskKrawtchoukCoeff 22 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_22_31 :
    maskKrawtchoukCoeff 22 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_23_0 :
    maskKrawtchoukCoeff 23 0 = 80 := by
  decide

theorem maskKrawtchoukCoeff_23_1 :
    maskKrawtchoukCoeff 23 1 = -80 := by
  decide

theorem maskKrawtchoukCoeff_23_2 :
    maskKrawtchoukCoeff 23 2 = -40 := by
  decide

theorem maskKrawtchoukCoeff_23_3 :
    maskKrawtchoukCoeff 23 3 = 40 := by
  decide

theorem maskKrawtchoukCoeff_23_4 :
    maskKrawtchoukCoeff 23 4 = -20 := by
  decide

theorem maskKrawtchoukCoeff_23_5 :
    maskKrawtchoukCoeff 23 5 = 20 := by
  decide

theorem maskKrawtchoukCoeff_23_6 :
    maskKrawtchoukCoeff 23 6 = 10 := by
  decide

theorem maskKrawtchoukCoeff_23_7 :
    maskKrawtchoukCoeff 23 7 = -10 := by
  decide

theorem maskKrawtchoukCoeff_23_8 :
    maskKrawtchoukCoeff 23 8 = 80 := by
  decide

theorem maskKrawtchoukCoeff_23_9 :
    maskKrawtchoukCoeff 23 9 = -80 := by
  decide

theorem maskKrawtchoukCoeff_23_10 :
    maskKrawtchoukCoeff 23 10 = -40 := by
  decide

theorem maskKrawtchoukCoeff_23_11 :
    maskKrawtchoukCoeff 23 11 = 40 := by
  decide

theorem maskKrawtchoukCoeff_23_12 :
    maskKrawtchoukCoeff 23 12 = -20 := by
  decide

theorem maskKrawtchoukCoeff_23_13 :
    maskKrawtchoukCoeff 23 13 = 20 := by
  decide

theorem maskKrawtchoukCoeff_23_14 :
    maskKrawtchoukCoeff 23 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_23_15 :
    maskKrawtchoukCoeff 23 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_23_16 :
    maskKrawtchoukCoeff 23 16 = -8 := by
  decide

theorem maskKrawtchoukCoeff_23_17 :
    maskKrawtchoukCoeff 23 17 = 8 := by
  decide

theorem maskKrawtchoukCoeff_23_18 :
    maskKrawtchoukCoeff 23 18 = 4 := by
  decide

theorem maskKrawtchoukCoeff_23_19 :
    maskKrawtchoukCoeff 23 19 = -4 := by
  decide

theorem maskKrawtchoukCoeff_23_20 :
    maskKrawtchoukCoeff 23 20 = 2 := by
  decide

theorem maskKrawtchoukCoeff_23_21 :
    maskKrawtchoukCoeff 23 21 = -2 := by
  decide

theorem maskKrawtchoukCoeff_23_22 :
    maskKrawtchoukCoeff 23 22 = -1 := by
  decide

theorem maskKrawtchoukCoeff_23_23 :
    maskKrawtchoukCoeff 23 23 = 1 := by
  decide

theorem maskKrawtchoukCoeff_23_24 :
    maskKrawtchoukCoeff 23 24 = -8 := by
  decide

theorem maskKrawtchoukCoeff_23_25 :
    maskKrawtchoukCoeff 23 25 = 8 := by
  decide

theorem maskKrawtchoukCoeff_23_26 :
    maskKrawtchoukCoeff 23 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_23_27 :
    maskKrawtchoukCoeff 23 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_23_28 :
    maskKrawtchoukCoeff 23 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_23_29 :
    maskKrawtchoukCoeff 23 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_23_30 :
    maskKrawtchoukCoeff 23 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_23_31 :
    maskKrawtchoukCoeff 23 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_0 :
    maskKrawtchoukCoeff 24 0 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_1 :
    maskKrawtchoukCoeff 24 1 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_2 :
    maskKrawtchoukCoeff 24 2 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_3 :
    maskKrawtchoukCoeff 24 3 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_4 :
    maskKrawtchoukCoeff 24 4 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_5 :
    maskKrawtchoukCoeff 24 5 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_6 :
    maskKrawtchoukCoeff 24 6 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_7 :
    maskKrawtchoukCoeff 24 7 = 60 := by
  decide

theorem maskKrawtchoukCoeff_24_8 :
    maskKrawtchoukCoeff 24 8 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_9 :
    maskKrawtchoukCoeff 24 9 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_10 :
    maskKrawtchoukCoeff 24 10 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_11 :
    maskKrawtchoukCoeff 24 11 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_12 :
    maskKrawtchoukCoeff 24 12 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_13 :
    maskKrawtchoukCoeff 24 13 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_14 :
    maskKrawtchoukCoeff 24 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_15 :
    maskKrawtchoukCoeff 24 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_24_16 :
    maskKrawtchoukCoeff 24 16 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_17 :
    maskKrawtchoukCoeff 24 17 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_18 :
    maskKrawtchoukCoeff 24 18 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_19 :
    maskKrawtchoukCoeff 24 19 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_20 :
    maskKrawtchoukCoeff 24 20 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_21 :
    maskKrawtchoukCoeff 24 21 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_22 :
    maskKrawtchoukCoeff 24 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_23 :
    maskKrawtchoukCoeff 24 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_24_24 :
    maskKrawtchoukCoeff 24 24 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_25 :
    maskKrawtchoukCoeff 24 25 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_26 :
    maskKrawtchoukCoeff 24 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_27 :
    maskKrawtchoukCoeff 24 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_28 :
    maskKrawtchoukCoeff 24 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_29 :
    maskKrawtchoukCoeff 24 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_30 :
    maskKrawtchoukCoeff 24 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_24_31 :
    maskKrawtchoukCoeff 24 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_25_0 :
    maskKrawtchoukCoeff 25 0 = 60 := by
  decide

theorem maskKrawtchoukCoeff_25_1 :
    maskKrawtchoukCoeff 25 1 = -60 := by
  decide

theorem maskKrawtchoukCoeff_25_2 :
    maskKrawtchoukCoeff 25 2 = 60 := by
  decide

theorem maskKrawtchoukCoeff_25_3 :
    maskKrawtchoukCoeff 25 3 = -60 := by
  decide

theorem maskKrawtchoukCoeff_25_4 :
    maskKrawtchoukCoeff 25 4 = 60 := by
  decide

theorem maskKrawtchoukCoeff_25_5 :
    maskKrawtchoukCoeff 25 5 = -60 := by
  decide

theorem maskKrawtchoukCoeff_25_6 :
    maskKrawtchoukCoeff 25 6 = 60 := by
  decide

theorem maskKrawtchoukCoeff_25_7 :
    maskKrawtchoukCoeff 25 7 = -60 := by
  decide

theorem maskKrawtchoukCoeff_25_8 :
    maskKrawtchoukCoeff 25 8 = -10 := by
  decide

theorem maskKrawtchoukCoeff_25_9 :
    maskKrawtchoukCoeff 25 9 = 10 := by
  decide

theorem maskKrawtchoukCoeff_25_10 :
    maskKrawtchoukCoeff 25 10 = -10 := by
  decide

theorem maskKrawtchoukCoeff_25_11 :
    maskKrawtchoukCoeff 25 11 = 10 := by
  decide

theorem maskKrawtchoukCoeff_25_12 :
    maskKrawtchoukCoeff 25 12 = -10 := by
  decide

theorem maskKrawtchoukCoeff_25_13 :
    maskKrawtchoukCoeff 25 13 = 10 := by
  decide

theorem maskKrawtchoukCoeff_25_14 :
    maskKrawtchoukCoeff 25 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_25_15 :
    maskKrawtchoukCoeff 25 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_25_16 :
    maskKrawtchoukCoeff 25 16 = -6 := by
  decide

theorem maskKrawtchoukCoeff_25_17 :
    maskKrawtchoukCoeff 25 17 = 6 := by
  decide

theorem maskKrawtchoukCoeff_25_18 :
    maskKrawtchoukCoeff 25 18 = -6 := by
  decide

theorem maskKrawtchoukCoeff_25_19 :
    maskKrawtchoukCoeff 25 19 = 6 := by
  decide

theorem maskKrawtchoukCoeff_25_20 :
    maskKrawtchoukCoeff 25 20 = -6 := by
  decide

theorem maskKrawtchoukCoeff_25_21 :
    maskKrawtchoukCoeff 25 21 = 6 := by
  decide

theorem maskKrawtchoukCoeff_25_22 :
    maskKrawtchoukCoeff 25 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_25_23 :
    maskKrawtchoukCoeff 25 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_25_24 :
    maskKrawtchoukCoeff 25 24 = 1 := by
  decide

theorem maskKrawtchoukCoeff_25_25 :
    maskKrawtchoukCoeff 25 25 = -1 := by
  decide

theorem maskKrawtchoukCoeff_25_26 :
    maskKrawtchoukCoeff 25 26 = 1 := by
  decide

theorem maskKrawtchoukCoeff_25_27 :
    maskKrawtchoukCoeff 25 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_25_28 :
    maskKrawtchoukCoeff 25 28 = 1 := by
  decide

theorem maskKrawtchoukCoeff_25_29 :
    maskKrawtchoukCoeff 25 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_25_30 :
    maskKrawtchoukCoeff 25 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_25_31 :
    maskKrawtchoukCoeff 25 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_26_0 :
    maskKrawtchoukCoeff 26 0 = 120 := by
  decide

theorem maskKrawtchoukCoeff_26_1 :
    maskKrawtchoukCoeff 26 1 = 120 := by
  decide

theorem maskKrawtchoukCoeff_26_2 :
    maskKrawtchoukCoeff 26 2 = -60 := by
  decide

theorem maskKrawtchoukCoeff_26_3 :
    maskKrawtchoukCoeff 26 3 = -60 := by
  decide

theorem maskKrawtchoukCoeff_26_4 :
    maskKrawtchoukCoeff 26 4 = 120 := by
  decide

theorem maskKrawtchoukCoeff_26_5 :
    maskKrawtchoukCoeff 26 5 = 120 := by
  decide

theorem maskKrawtchoukCoeff_26_6 :
    maskKrawtchoukCoeff 26 6 = -60 := by
  decide

theorem maskKrawtchoukCoeff_26_7 :
    maskKrawtchoukCoeff 26 7 = -60 := by
  decide

theorem maskKrawtchoukCoeff_26_8 :
    maskKrawtchoukCoeff 26 8 = -20 := by
  decide

theorem maskKrawtchoukCoeff_26_9 :
    maskKrawtchoukCoeff 26 9 = -20 := by
  decide

theorem maskKrawtchoukCoeff_26_10 :
    maskKrawtchoukCoeff 26 10 = 10 := by
  decide

theorem maskKrawtchoukCoeff_26_11 :
    maskKrawtchoukCoeff 26 11 = 10 := by
  decide

theorem maskKrawtchoukCoeff_26_12 :
    maskKrawtchoukCoeff 26 12 = -20 := by
  decide

theorem maskKrawtchoukCoeff_26_13 :
    maskKrawtchoukCoeff 26 13 = -20 := by
  decide

theorem maskKrawtchoukCoeff_26_14 :
    maskKrawtchoukCoeff 26 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_26_15 :
    maskKrawtchoukCoeff 26 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_26_16 :
    maskKrawtchoukCoeff 26 16 = -12 := by
  decide

theorem maskKrawtchoukCoeff_26_17 :
    maskKrawtchoukCoeff 26 17 = -12 := by
  decide

theorem maskKrawtchoukCoeff_26_18 :
    maskKrawtchoukCoeff 26 18 = 6 := by
  decide

theorem maskKrawtchoukCoeff_26_19 :
    maskKrawtchoukCoeff 26 19 = 6 := by
  decide

theorem maskKrawtchoukCoeff_26_20 :
    maskKrawtchoukCoeff 26 20 = -12 := by
  decide

theorem maskKrawtchoukCoeff_26_21 :
    maskKrawtchoukCoeff 26 21 = -12 := by
  decide

theorem maskKrawtchoukCoeff_26_22 :
    maskKrawtchoukCoeff 26 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_26_23 :
    maskKrawtchoukCoeff 26 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_26_24 :
    maskKrawtchoukCoeff 26 24 = 2 := by
  decide

theorem maskKrawtchoukCoeff_26_25 :
    maskKrawtchoukCoeff 26 25 = 2 := by
  decide

theorem maskKrawtchoukCoeff_26_26 :
    maskKrawtchoukCoeff 26 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_26_27 :
    maskKrawtchoukCoeff 26 27 = -1 := by
  decide

theorem maskKrawtchoukCoeff_26_28 :
    maskKrawtchoukCoeff 26 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_26_29 :
    maskKrawtchoukCoeff 26 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_26_30 :
    maskKrawtchoukCoeff 26 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_26_31 :
    maskKrawtchoukCoeff 26 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_27_0 :
    maskKrawtchoukCoeff 27 0 = 120 := by
  decide

theorem maskKrawtchoukCoeff_27_1 :
    maskKrawtchoukCoeff 27 1 = -120 := by
  decide

theorem maskKrawtchoukCoeff_27_2 :
    maskKrawtchoukCoeff 27 2 = -60 := by
  decide

theorem maskKrawtchoukCoeff_27_3 :
    maskKrawtchoukCoeff 27 3 = 60 := by
  decide

theorem maskKrawtchoukCoeff_27_4 :
    maskKrawtchoukCoeff 27 4 = 120 := by
  decide

theorem maskKrawtchoukCoeff_27_5 :
    maskKrawtchoukCoeff 27 5 = -120 := by
  decide

theorem maskKrawtchoukCoeff_27_6 :
    maskKrawtchoukCoeff 27 6 = -60 := by
  decide

theorem maskKrawtchoukCoeff_27_7 :
    maskKrawtchoukCoeff 27 7 = 60 := by
  decide

theorem maskKrawtchoukCoeff_27_8 :
    maskKrawtchoukCoeff 27 8 = -20 := by
  decide

theorem maskKrawtchoukCoeff_27_9 :
    maskKrawtchoukCoeff 27 9 = 20 := by
  decide

theorem maskKrawtchoukCoeff_27_10 :
    maskKrawtchoukCoeff 27 10 = 10 := by
  decide

theorem maskKrawtchoukCoeff_27_11 :
    maskKrawtchoukCoeff 27 11 = -10 := by
  decide

theorem maskKrawtchoukCoeff_27_12 :
    maskKrawtchoukCoeff 27 12 = -20 := by
  decide

theorem maskKrawtchoukCoeff_27_13 :
    maskKrawtchoukCoeff 27 13 = 20 := by
  decide

theorem maskKrawtchoukCoeff_27_14 :
    maskKrawtchoukCoeff 27 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_27_15 :
    maskKrawtchoukCoeff 27 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_27_16 :
    maskKrawtchoukCoeff 27 16 = -12 := by
  decide

theorem maskKrawtchoukCoeff_27_17 :
    maskKrawtchoukCoeff 27 17 = 12 := by
  decide

theorem maskKrawtchoukCoeff_27_18 :
    maskKrawtchoukCoeff 27 18 = 6 := by
  decide

theorem maskKrawtchoukCoeff_27_19 :
    maskKrawtchoukCoeff 27 19 = -6 := by
  decide

theorem maskKrawtchoukCoeff_27_20 :
    maskKrawtchoukCoeff 27 20 = -12 := by
  decide

theorem maskKrawtchoukCoeff_27_21 :
    maskKrawtchoukCoeff 27 21 = 12 := by
  decide

theorem maskKrawtchoukCoeff_27_22 :
    maskKrawtchoukCoeff 27 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_27_23 :
    maskKrawtchoukCoeff 27 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_27_24 :
    maskKrawtchoukCoeff 27 24 = 2 := by
  decide

theorem maskKrawtchoukCoeff_27_25 :
    maskKrawtchoukCoeff 27 25 = -2 := by
  decide

theorem maskKrawtchoukCoeff_27_26 :
    maskKrawtchoukCoeff 27 26 = -1 := by
  decide

theorem maskKrawtchoukCoeff_27_27 :
    maskKrawtchoukCoeff 27 27 = 1 := by
  decide

theorem maskKrawtchoukCoeff_27_28 :
    maskKrawtchoukCoeff 27 28 = 2 := by
  decide

theorem maskKrawtchoukCoeff_27_29 :
    maskKrawtchoukCoeff 27 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_27_30 :
    maskKrawtchoukCoeff 27 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_27_31 :
    maskKrawtchoukCoeff 27 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_28_0 :
    maskKrawtchoukCoeff 28 0 = 240 := by
  decide

theorem maskKrawtchoukCoeff_28_1 :
    maskKrawtchoukCoeff 28 1 = 240 := by
  decide

theorem maskKrawtchoukCoeff_28_2 :
    maskKrawtchoukCoeff 28 2 = 240 := by
  decide

theorem maskKrawtchoukCoeff_28_3 :
    maskKrawtchoukCoeff 28 3 = 240 := by
  decide

theorem maskKrawtchoukCoeff_28_4 :
    maskKrawtchoukCoeff 28 4 = -60 := by
  decide

theorem maskKrawtchoukCoeff_28_5 :
    maskKrawtchoukCoeff 28 5 = -60 := by
  decide

theorem maskKrawtchoukCoeff_28_6 :
    maskKrawtchoukCoeff 28 6 = -60 := by
  decide

theorem maskKrawtchoukCoeff_28_7 :
    maskKrawtchoukCoeff 28 7 = -60 := by
  decide

theorem maskKrawtchoukCoeff_28_8 :
    maskKrawtchoukCoeff 28 8 = -40 := by
  decide

theorem maskKrawtchoukCoeff_28_9 :
    maskKrawtchoukCoeff 28 9 = -40 := by
  decide

theorem maskKrawtchoukCoeff_28_10 :
    maskKrawtchoukCoeff 28 10 = -40 := by
  decide

theorem maskKrawtchoukCoeff_28_11 :
    maskKrawtchoukCoeff 28 11 = -40 := by
  decide

theorem maskKrawtchoukCoeff_28_12 :
    maskKrawtchoukCoeff 28 12 = 10 := by
  decide

theorem maskKrawtchoukCoeff_28_13 :
    maskKrawtchoukCoeff 28 13 = 10 := by
  decide

theorem maskKrawtchoukCoeff_28_14 :
    maskKrawtchoukCoeff 28 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_28_15 :
    maskKrawtchoukCoeff 28 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_28_16 :
    maskKrawtchoukCoeff 28 16 = -24 := by
  decide

theorem maskKrawtchoukCoeff_28_17 :
    maskKrawtchoukCoeff 28 17 = -24 := by
  decide

theorem maskKrawtchoukCoeff_28_18 :
    maskKrawtchoukCoeff 28 18 = -24 := by
  decide

theorem maskKrawtchoukCoeff_28_19 :
    maskKrawtchoukCoeff 28 19 = -24 := by
  decide

theorem maskKrawtchoukCoeff_28_20 :
    maskKrawtchoukCoeff 28 20 = 6 := by
  decide

theorem maskKrawtchoukCoeff_28_21 :
    maskKrawtchoukCoeff 28 21 = 6 := by
  decide

theorem maskKrawtchoukCoeff_28_22 :
    maskKrawtchoukCoeff 28 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_28_23 :
    maskKrawtchoukCoeff 28 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_28_24 :
    maskKrawtchoukCoeff 28 24 = 4 := by
  decide

theorem maskKrawtchoukCoeff_28_25 :
    maskKrawtchoukCoeff 28 25 = 4 := by
  decide

theorem maskKrawtchoukCoeff_28_26 :
    maskKrawtchoukCoeff 28 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_28_27 :
    maskKrawtchoukCoeff 28 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_28_28 :
    maskKrawtchoukCoeff 28 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_28_29 :
    maskKrawtchoukCoeff 28 29 = -1 := by
  decide

theorem maskKrawtchoukCoeff_28_30 :
    maskKrawtchoukCoeff 28 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_28_31 :
    maskKrawtchoukCoeff 28 31 = -1 := by
  decide

theorem maskKrawtchoukCoeff_29_0 :
    maskKrawtchoukCoeff 29 0 = 240 := by
  decide

theorem maskKrawtchoukCoeff_29_1 :
    maskKrawtchoukCoeff 29 1 = -240 := by
  decide

theorem maskKrawtchoukCoeff_29_2 :
    maskKrawtchoukCoeff 29 2 = 240 := by
  decide

theorem maskKrawtchoukCoeff_29_3 :
    maskKrawtchoukCoeff 29 3 = -240 := by
  decide

theorem maskKrawtchoukCoeff_29_4 :
    maskKrawtchoukCoeff 29 4 = -60 := by
  decide

theorem maskKrawtchoukCoeff_29_5 :
    maskKrawtchoukCoeff 29 5 = 60 := by
  decide

theorem maskKrawtchoukCoeff_29_6 :
    maskKrawtchoukCoeff 29 6 = -60 := by
  decide

theorem maskKrawtchoukCoeff_29_7 :
    maskKrawtchoukCoeff 29 7 = 60 := by
  decide

theorem maskKrawtchoukCoeff_29_8 :
    maskKrawtchoukCoeff 29 8 = -40 := by
  decide

theorem maskKrawtchoukCoeff_29_9 :
    maskKrawtchoukCoeff 29 9 = 40 := by
  decide

theorem maskKrawtchoukCoeff_29_10 :
    maskKrawtchoukCoeff 29 10 = -40 := by
  decide

theorem maskKrawtchoukCoeff_29_11 :
    maskKrawtchoukCoeff 29 11 = 40 := by
  decide

theorem maskKrawtchoukCoeff_29_12 :
    maskKrawtchoukCoeff 29 12 = 10 := by
  decide

theorem maskKrawtchoukCoeff_29_13 :
    maskKrawtchoukCoeff 29 13 = -10 := by
  decide

theorem maskKrawtchoukCoeff_29_14 :
    maskKrawtchoukCoeff 29 14 = 10 := by
  decide

theorem maskKrawtchoukCoeff_29_15 :
    maskKrawtchoukCoeff 29 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_29_16 :
    maskKrawtchoukCoeff 29 16 = -24 := by
  decide

theorem maskKrawtchoukCoeff_29_17 :
    maskKrawtchoukCoeff 29 17 = 24 := by
  decide

theorem maskKrawtchoukCoeff_29_18 :
    maskKrawtchoukCoeff 29 18 = -24 := by
  decide

theorem maskKrawtchoukCoeff_29_19 :
    maskKrawtchoukCoeff 29 19 = 24 := by
  decide

theorem maskKrawtchoukCoeff_29_20 :
    maskKrawtchoukCoeff 29 20 = 6 := by
  decide

theorem maskKrawtchoukCoeff_29_21 :
    maskKrawtchoukCoeff 29 21 = -6 := by
  decide

theorem maskKrawtchoukCoeff_29_22 :
    maskKrawtchoukCoeff 29 22 = 6 := by
  decide

theorem maskKrawtchoukCoeff_29_23 :
    maskKrawtchoukCoeff 29 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_29_24 :
    maskKrawtchoukCoeff 29 24 = 4 := by
  decide

theorem maskKrawtchoukCoeff_29_25 :
    maskKrawtchoukCoeff 29 25 = -4 := by
  decide

theorem maskKrawtchoukCoeff_29_26 :
    maskKrawtchoukCoeff 29 26 = 4 := by
  decide

theorem maskKrawtchoukCoeff_29_27 :
    maskKrawtchoukCoeff 29 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_29_28 :
    maskKrawtchoukCoeff 29 28 = -1 := by
  decide

theorem maskKrawtchoukCoeff_29_29 :
    maskKrawtchoukCoeff 29 29 = 1 := by
  decide

theorem maskKrawtchoukCoeff_29_30 :
    maskKrawtchoukCoeff 29 30 = -1 := by
  decide

theorem maskKrawtchoukCoeff_29_31 :
    maskKrawtchoukCoeff 29 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_30_0 :
    maskKrawtchoukCoeff 30 0 = 480 := by
  decide

theorem maskKrawtchoukCoeff_30_1 :
    maskKrawtchoukCoeff 30 1 = 480 := by
  decide

theorem maskKrawtchoukCoeff_30_2 :
    maskKrawtchoukCoeff 30 2 = -240 := by
  decide

theorem maskKrawtchoukCoeff_30_3 :
    maskKrawtchoukCoeff 30 3 = -240 := by
  decide

theorem maskKrawtchoukCoeff_30_4 :
    maskKrawtchoukCoeff 30 4 = -120 := by
  decide

theorem maskKrawtchoukCoeff_30_5 :
    maskKrawtchoukCoeff 30 5 = -120 := by
  decide

theorem maskKrawtchoukCoeff_30_6 :
    maskKrawtchoukCoeff 30 6 = 60 := by
  decide

theorem maskKrawtchoukCoeff_30_7 :
    maskKrawtchoukCoeff 30 7 = 60 := by
  decide

theorem maskKrawtchoukCoeff_30_8 :
    maskKrawtchoukCoeff 30 8 = -80 := by
  decide

theorem maskKrawtchoukCoeff_30_9 :
    maskKrawtchoukCoeff 30 9 = -80 := by
  decide

theorem maskKrawtchoukCoeff_30_10 :
    maskKrawtchoukCoeff 30 10 = 40 := by
  decide

theorem maskKrawtchoukCoeff_30_11 :
    maskKrawtchoukCoeff 30 11 = 40 := by
  decide

theorem maskKrawtchoukCoeff_30_12 :
    maskKrawtchoukCoeff 30 12 = 20 := by
  decide

theorem maskKrawtchoukCoeff_30_13 :
    maskKrawtchoukCoeff 30 13 = 20 := by
  decide

theorem maskKrawtchoukCoeff_30_14 :
    maskKrawtchoukCoeff 30 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_30_15 :
    maskKrawtchoukCoeff 30 15 = -10 := by
  decide

theorem maskKrawtchoukCoeff_30_16 :
    maskKrawtchoukCoeff 30 16 = -48 := by
  decide

theorem maskKrawtchoukCoeff_30_17 :
    maskKrawtchoukCoeff 30 17 = -48 := by
  decide

theorem maskKrawtchoukCoeff_30_18 :
    maskKrawtchoukCoeff 30 18 = 24 := by
  decide

theorem maskKrawtchoukCoeff_30_19 :
    maskKrawtchoukCoeff 30 19 = 24 := by
  decide

theorem maskKrawtchoukCoeff_30_20 :
    maskKrawtchoukCoeff 30 20 = 12 := by
  decide

theorem maskKrawtchoukCoeff_30_21 :
    maskKrawtchoukCoeff 30 21 = 12 := by
  decide

theorem maskKrawtchoukCoeff_30_22 :
    maskKrawtchoukCoeff 30 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_30_23 :
    maskKrawtchoukCoeff 30 23 = -6 := by
  decide

theorem maskKrawtchoukCoeff_30_24 :
    maskKrawtchoukCoeff 30 24 = 8 := by
  decide

theorem maskKrawtchoukCoeff_30_25 :
    maskKrawtchoukCoeff 30 25 = 8 := by
  decide

theorem maskKrawtchoukCoeff_30_26 :
    maskKrawtchoukCoeff 30 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_30_27 :
    maskKrawtchoukCoeff 30 27 = -4 := by
  decide

theorem maskKrawtchoukCoeff_30_28 :
    maskKrawtchoukCoeff 30 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_30_29 :
    maskKrawtchoukCoeff 30 29 = -2 := by
  decide

theorem maskKrawtchoukCoeff_30_30 :
    maskKrawtchoukCoeff 30 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_30_31 :
    maskKrawtchoukCoeff 30 31 = 1 := by
  decide

theorem maskKrawtchoukCoeff_31_0 :
    maskKrawtchoukCoeff 31 0 = 480 := by
  decide

theorem maskKrawtchoukCoeff_31_1 :
    maskKrawtchoukCoeff 31 1 = -480 := by
  decide

theorem maskKrawtchoukCoeff_31_2 :
    maskKrawtchoukCoeff 31 2 = -240 := by
  decide

theorem maskKrawtchoukCoeff_31_3 :
    maskKrawtchoukCoeff 31 3 = 240 := by
  decide

theorem maskKrawtchoukCoeff_31_4 :
    maskKrawtchoukCoeff 31 4 = -120 := by
  decide

theorem maskKrawtchoukCoeff_31_5 :
    maskKrawtchoukCoeff 31 5 = 120 := by
  decide

theorem maskKrawtchoukCoeff_31_6 :
    maskKrawtchoukCoeff 31 6 = 60 := by
  decide

theorem maskKrawtchoukCoeff_31_7 :
    maskKrawtchoukCoeff 31 7 = -60 := by
  decide

theorem maskKrawtchoukCoeff_31_8 :
    maskKrawtchoukCoeff 31 8 = -80 := by
  decide

theorem maskKrawtchoukCoeff_31_9 :
    maskKrawtchoukCoeff 31 9 = 80 := by
  decide

theorem maskKrawtchoukCoeff_31_10 :
    maskKrawtchoukCoeff 31 10 = 40 := by
  decide

theorem maskKrawtchoukCoeff_31_11 :
    maskKrawtchoukCoeff 31 11 = -40 := by
  decide

theorem maskKrawtchoukCoeff_31_12 :
    maskKrawtchoukCoeff 31 12 = 20 := by
  decide

theorem maskKrawtchoukCoeff_31_13 :
    maskKrawtchoukCoeff 31 13 = -20 := by
  decide

theorem maskKrawtchoukCoeff_31_14 :
    maskKrawtchoukCoeff 31 14 = -10 := by
  decide

theorem maskKrawtchoukCoeff_31_15 :
    maskKrawtchoukCoeff 31 15 = 10 := by
  decide

theorem maskKrawtchoukCoeff_31_16 :
    maskKrawtchoukCoeff 31 16 = -48 := by
  decide

theorem maskKrawtchoukCoeff_31_17 :
    maskKrawtchoukCoeff 31 17 = 48 := by
  decide

theorem maskKrawtchoukCoeff_31_18 :
    maskKrawtchoukCoeff 31 18 = 24 := by
  decide

theorem maskKrawtchoukCoeff_31_19 :
    maskKrawtchoukCoeff 31 19 = -24 := by
  decide

theorem maskKrawtchoukCoeff_31_20 :
    maskKrawtchoukCoeff 31 20 = 12 := by
  decide

theorem maskKrawtchoukCoeff_31_21 :
    maskKrawtchoukCoeff 31 21 = -12 := by
  decide

theorem maskKrawtchoukCoeff_31_22 :
    maskKrawtchoukCoeff 31 22 = -6 := by
  decide

theorem maskKrawtchoukCoeff_31_23 :
    maskKrawtchoukCoeff 31 23 = 6 := by
  decide

theorem maskKrawtchoukCoeff_31_24 :
    maskKrawtchoukCoeff 31 24 = 8 := by
  decide

theorem maskKrawtchoukCoeff_31_25 :
    maskKrawtchoukCoeff 31 25 = -8 := by
  decide

theorem maskKrawtchoukCoeff_31_26 :
    maskKrawtchoukCoeff 31 26 = -4 := by
  decide

theorem maskKrawtchoukCoeff_31_27 :
    maskKrawtchoukCoeff 31 27 = 4 := by
  decide

theorem maskKrawtchoukCoeff_31_28 :
    maskKrawtchoukCoeff 31 28 = -2 := by
  decide

theorem maskKrawtchoukCoeff_31_29 :
    maskKrawtchoukCoeff 31 29 = 2 := by
  decide

theorem maskKrawtchoukCoeff_31_30 :
    maskKrawtchoukCoeff 31 30 = 1 := by
  decide

theorem maskKrawtchoukCoeff_31_31 :
    maskKrawtchoukCoeff 31 31 = -1 := by
  decide

private theorem axisSupportOfMask_fin_bijective :
    Function.Bijective (fun m : Fin 32 => axisSupportOfMask m.val) := by
  decide

private noncomputable def axisSupportMaskEquiv : Fin 32 ≃ AxisSupport2310 :=
  Equiv.ofBijective (fun m : Fin 32 => axisSupportOfMask m.val)
    axisSupportOfMask_fin_bijective

theorem sum_axisSupportOfMask (f : AxisSupport2310 → Int) :
    (∑ D : AxisSupport2310, f D) =
      ∑ m : Fin 32, f (axisSupportOfMask m.val) := by
  exact (Fintype.sum_equiv axisSupportMaskEquiv
    (fun m => f (axisSupportMaskEquiv m)) f (fun _ => rfl)).symm

theorem sum_axisSupportOfMask_explicit (f : AxisSupport2310 → Int) :
    (∑ D : AxisSupport2310, f D) =
      f (axisSupportOfMask 0) +
      f (axisSupportOfMask 1) +
      f (axisSupportOfMask 2) +
      f (axisSupportOfMask 3) +
      f (axisSupportOfMask 4) +
      f (axisSupportOfMask 5) +
      f (axisSupportOfMask 6) +
      f (axisSupportOfMask 7) +
      f (axisSupportOfMask 8) +
      f (axisSupportOfMask 9) +
      f (axisSupportOfMask 10) +
      f (axisSupportOfMask 11) +
      f (axisSupportOfMask 12) +
      f (axisSupportOfMask 13) +
      f (axisSupportOfMask 14) +
      f (axisSupportOfMask 15) +
      f (axisSupportOfMask 16) +
      f (axisSupportOfMask 17) +
      f (axisSupportOfMask 18) +
      f (axisSupportOfMask 19) +
      f (axisSupportOfMask 20) +
      f (axisSupportOfMask 21) +
      f (axisSupportOfMask 22) +
      f (axisSupportOfMask 23) +
      f (axisSupportOfMask 24) +
      f (axisSupportOfMask 25) +
      f (axisSupportOfMask 26) +
      f (axisSupportOfMask 27) +
      f (axisSupportOfMask 28) +
      f (axisSupportOfMask 29) +
      f (axisSupportOfMask 30) +
      f (axisSupportOfMask 31) := by
  rw [sum_axisSupportOfMask]
  norm_num [Fin.sum_univ_succ]
  ac_rfl

/-- Support modulus in a form whose concrete mask instances are decidable. -/
def maskSupportModulus (mask : Nat) : Nat :=
  ∏ i : Fin 5, if mask.testBit i.val then crt2310Modulus i else 1

theorem supportModulus_axisSupportOfMask (mask : Nat) :
    supportModulus (axisSupportOfMask mask) = maskSupportModulus mask := by
  simp [supportModulus, axisSupportOfMask, maskSupportModulus, Finset.prod_filter]

/-- Shared reduction of every balanced projection lower bound. -/
theorem balancedCollisionLower_axisSupportOfMask (k mask : Nat) :
    balancedCollisionLower k (supportModulus (axisSupportOfMask mask)) =
      balancedCollisionLower k (maskSupportModulus mask) := by
  rw [supportModulus_axisSupportOfMask]

/-- Shared reduction of every projection-capacity upper bound. -/
theorem projectionCapacityUpper_axisSupportOfMask (k mask : Nat) :
    projectionCapacityUpper k (supportModulus (axisSupportOfMask mask)) =
      projectionCapacityUpper k (maskSupportModulus mask) := by
  rw [supportModulus_axisSupportOfMask]

end Fuglede
