-- Generator SHA-256: 262ea73e5d8e73e5c7e4f711e26932138b9324c56bc0af818ce617ddd0cd05cd
import Fuglede.Z180K12M6ProjectedCompactKernel
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Fuglede

theorem z180_k12_m6_order9_compact_indicator_impossible
    (b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 k0 k1 : Int)
    (hlo_0 : (b_0 ≥ 0))
    (hhi_0 : (b_0 ≤ 1))
    (hlo_1 : (b_1 ≥ 0))
    (hhi_1 : (b_1 ≤ 1))
    (hlo_2 : (b_2 ≥ 0))
    (hhi_2 : (b_2 ≤ 1))
    (hlo_3 : (b_3 ≥ 0))
    (hhi_3 : (b_3 ≤ 1))
    (hlo_4 : (b_4 ≥ 0))
    (hhi_4 : (b_4 ≤ 1))
    (hlo_5 : (b_5 ≥ 0))
    (hhi_5 : (b_5 ≤ 1))
    (hlo_6 : (b_6 ≥ 0))
    (hhi_6 : (b_6 ≤ 1))
    (hlo_7 : (b_7 ≥ 0))
    (hhi_7 : (b_7 ≤ 1))
    (hlo_8 : (b_8 ≥ 0))
    (hhi_8 : (b_8 ≤ 1))
    (hlo_9 : (b_9 ≥ 0))
    (hhi_9 : (b_9 ≤ 1))
    (hlo_10 : (b_10 ≥ 0))
    (hhi_10 : (b_10 ≤ 1))
    (hlo_11 : (b_11 ≥ 0))
    (hhi_11 : (b_11 ≤ 1))
    (hlo_12 : (b_12 ≥ 0))
    (hhi_12 : (b_12 ≤ 1))
    (hlo_13 : (b_13 ≥ 0))
    (hhi_13 : (b_13 ≤ 1))
    (hlo_14 : (b_14 ≥ 0))
    (hhi_14 : (b_14 ≤ 1))
    (hlo_15 : (b_15 ≥ 0))
    (hhi_15 : (b_15 ≤ 1))
    (hlo_16 : (b_16 ≥ 0))
    (hhi_16 : (b_16 ≤ 1))
    (hlo_17 : (b_17 ≥ 0))
    (hhi_17 : (b_17 ≤ 1))
    (hlo_18 : (b_18 ≥ 0))
    (hhi_18 : (b_18 ≤ 1))
    (hlo_19 : (b_19 ≥ 0))
    (hhi_19 : (b_19 ≤ 1))
    (hlo_20 : (b_20 ≥ 0))
    (hhi_20 : (b_20 ≤ 1))
    (hlo_21 : (b_21 ≥ 0))
    (hhi_21 : (b_21 ≤ 1))
    (hlo_22 : (b_22 ≥ 0))
    (hhi_22 : (b_22 ≤ 1))
    (hlo_23 : (b_23 ≥ 0))
    (hhi_23 : (b_23 ≤ 1))
    (hlo_24 : (b_24 ≥ 0))
    (hhi_24 : (b_24 ≤ 1))
    (hlo_25 : (b_25 ≥ 0))
    (hhi_25 : (b_25 ≤ 1))
    (hlo_26 : (b_26 ≥ 0))
    (hhi_26 : (b_26 ≤ 1))
    (hlo_27 : (b_27 ≥ 0))
    (hhi_27 : (b_27 ≤ 1))
    (hlo_28 : (b_28 ≥ 0))
    (hhi_28 : (b_28 ≤ 1))
    (hlo_29 : (b_29 ≥ 0))
    (hhi_29 : (b_29 ≤ 1))
    (hlo_30 : (b_30 ≥ 0))
    (hhi_30 : (b_30 ≤ 1))
    (hlo_31 : (b_31 ≥ 0))
    (hhi_31 : (b_31 ≤ 1))
    (hlo_32 : (b_32 ≥ 0))
    (hhi_32 : (b_32 ≤ 1))
    (hlo_33 : (b_33 ≥ 0))
    (hhi_33 : (b_33 ≤ 1))
    (hlo_34 : (b_34 ≥ 0))
    (hhi_34 : (b_34 ≤ 1))
    (hlo_35 : (b_35 ≥ 0))
    (hhi_35 : (b_35 ≤ 1))
    (hmod4_0 : ((b_0 + b_4 + b_8 + b_12 + b_16 + b_20 + b_24 + b_28 + b_32) = 3))
    (hmod4_1 : ((b_1 + b_5 + b_9 + b_13 + b_17 + b_21 + b_25 + b_29 + b_33) = 3))
    (hmod4_2 : ((b_2 + b_6 + b_10 + b_14 + b_18 + b_22 + b_26 + b_30 + b_34) = 3))
    (hmod4_3 : ((b_3 + b_7 + b_11 + b_15 + b_19 + b_23 + b_27 + b_31 + b_35) = 3))
    (hphi9_0 : (((b_0 * 1) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * (-1)) + (b_7 * 0) + (b_8 * 0) + (b_9 * 1) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 0) + (b_18 * 1) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * (-1)) + (b_25 * 0) + (b_26 * 0) + (b_27 * 1) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 0)) = 0))
    (hphi9_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * 0) + (b_7 * (-1)) + (b_8 * 0) + (b_9 * 0) + (b_10 * 1) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * 0) + (b_18 * 0) + (b_19 * 1) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * 0) + (b_25 * (-1)) + (b_26 * 0) + (b_27 * 0) + (b_28 * 1) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * 0)) = 0))
    (hphi9_2 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 1) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * 0) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * 0) + (b_10 * 0) + (b_11 * 1) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * 0) + (b_16 * 0) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 0) + (b_20 * 1) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * 0) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * 0) + (b_28 * 0) + (b_29 * 1) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * 0) + (b_34 * 0) + (b_35 * (-1))) = 0))
    (hphi9_3 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 1) + (b_4 * 0) + (b_5 * 0) + (b_6 * (-1)) + (b_7 * 0) + (b_8 * 0) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * 1) + (b_13 * 0) + (b_14 * 0) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 0) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 1) + (b_22 * 0) + (b_23 * 0) + (b_24 * (-1)) + (b_25 * 0) + (b_26 * 0) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * 1) + (b_31 * 0) + (b_32 * 0) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 0)) = 0))
    (hphi9_4 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 1) + (b_5 * 0) + (b_6 * 0) + (b_7 * (-1)) + (b_8 * 0) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * 1) + (b_14 * 0) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * 0) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 1) + (b_23 * 0) + (b_24 * 0) + (b_25 * (-1)) + (b_26 * 0) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * 1) + (b_32 * 0) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * 0)) = 0))
    (hphi9_5 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 1) + (b_6 * 0) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * 1) + (b_15 * 0) + (b_16 * 0) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 1) + (b_24 * 0) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * 1) + (b_33 * 0) + (b_34 * 0) + (b_35 * (-1))) = 0))
    (hphi6_0 : ((b_0 * (1)) + (b_1 * (0)) + (b_2 * (-1)) + (b_3 * (-1)) + (b_4 * (0)) + (b_5 * (1)) + (b_6 * (1)) + (b_7 * (0)) + (b_8 * (-1)) + (b_9 * (-1)) + (b_10 * (0)) + (b_11 * (1)) + (b_12 * (1)) + (b_13 * (0)) + (b_14 * (-1)) + (b_15 * (-1)) + (b_16 * (0)) + (b_17 * (1)) + (b_18 * (1)) + (b_19 * (0)) + (b_20 * (-1)) + (b_21 * (-1)) + (b_22 * (0)) + (b_23 * (1)) + (b_24 * (1)) + (b_25 * (0)) + (b_26 * (-1)) + (b_27 * (-1)) + (b_28 * (0)) + (b_29 * (1)) + (b_30 * (1)) + (b_31 * (0)) + (b_32 * (-1)) + (b_33 * (-1)) + (b_34 * (0)) + (b_35 * (1))) = 5 * k0)
    (hphi6_1 : ((b_0 * (0)) + (b_1 * (1)) + (b_2 * (1)) + (b_3 * (0)) + (b_4 * (-1)) + (b_5 * (-1)) + (b_6 * (0)) + (b_7 * (1)) + (b_8 * (1)) + (b_9 * (0)) + (b_10 * (-1)) + (b_11 * (-1)) + (b_12 * (0)) + (b_13 * (1)) + (b_14 * (1)) + (b_15 * (0)) + (b_16 * (-1)) + (b_17 * (-1)) + (b_18 * (0)) + (b_19 * (1)) + (b_20 * (1)) + (b_21 * (0)) + (b_22 * (-1)) + (b_23 * (-1)) + (b_24 * (0)) + (b_25 * (1)) + (b_26 * (1)) + (b_27 * (0)) + (b_28 * (-1)) + (b_29 * (-1)) + (b_30 * (0)) + (b_31 * (1)) + (b_32 * (1)) + (b_33 * (0)) + (b_34 * (-1)) + (b_35 * (-1))) = 5 * k1)
    (hphi6_ne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  let E0 : Int := b_0 + b_6 + b_12 + b_18 + b_24 + b_30
  let O0 : Int := b_3 + b_9 + b_15 + b_21 + b_27 + b_33
  let n0 : Int := b_0 + b_9 + b_18 + b_27
  have hE0lo : 0 ≤ E0 := by
    dsimp only [E0]
    linarith only [hlo_0, hlo_6, hlo_12, hlo_18, hlo_24, hlo_30]
  have hE0hi : E0 ≤ 6 := by
    dsimp only [E0]
    linarith only [hhi_0, hhi_6, hhi_12, hhi_18, hhi_24, hhi_30]
  have hO0lo : 0 ≤ O0 := by
    dsimp only [O0]
    linarith only [hlo_3, hlo_9, hlo_15, hlo_21, hlo_27, hlo_33]
  have hO0hi : O0 ≤ 6 := by
    dsimp only [O0]
    linarith only [hhi_3, hhi_9, hhi_15, hhi_21, hhi_27, hhi_33]
  have hclass0 : E0 + O0 = 3 * n0 := by
    dsimp only [E0, O0, n0]
    linarith only [hphi9_0, hphi9_3]
  let E1 : Int := b_4 + b_10 + b_16 + b_22 + b_28 + b_34
  let O1 : Int := b_1 + b_7 + b_13 + b_19 + b_25 + b_31
  let n1 : Int := b_1 + b_10 + b_19 + b_28
  have hE1lo : 0 ≤ E1 := by
    dsimp only [E1]
    linarith only [hlo_4, hlo_10, hlo_16, hlo_22, hlo_28, hlo_34]
  have hE1hi : E1 ≤ 6 := by
    dsimp only [E1]
    linarith only [hhi_4, hhi_10, hhi_16, hhi_22, hhi_28, hhi_34]
  have hO1lo : 0 ≤ O1 := by
    dsimp only [O1]
    linarith only [hlo_1, hlo_7, hlo_13, hlo_19, hlo_25, hlo_31]
  have hO1hi : O1 ≤ 6 := by
    dsimp only [O1]
    linarith only [hhi_1, hhi_7, hhi_13, hhi_19, hhi_25, hhi_31]
  have hclass1 : E1 + O1 = 3 * n1 := by
    dsimp only [E1, O1, n1]
    linarith only [hphi9_1, hphi9_4]
  let E2 : Int := b_2 + b_8 + b_14 + b_20 + b_26 + b_32
  let O2 : Int := b_5 + b_11 + b_17 + b_23 + b_29 + b_35
  let n2 : Int := b_2 + b_11 + b_20 + b_29
  have hE2lo : 0 ≤ E2 := by
    dsimp only [E2]
    linarith only [hlo_2, hlo_8, hlo_14, hlo_20, hlo_26, hlo_32]
  have hE2hi : E2 ≤ 6 := by
    dsimp only [E2]
    linarith only [hhi_2, hhi_8, hhi_14, hhi_20, hhi_26, hhi_32]
  have hO2lo : 0 ≤ O2 := by
    dsimp only [O2]
    linarith only [hlo_5, hlo_11, hlo_17, hlo_23, hlo_29, hlo_35]
  have hO2hi : O2 ≤ 6 := by
    dsimp only [O2]
    linarith only [hhi_5, hhi_11, hhi_17, hhi_23, hhi_29, hhi_35]
  have hclass2 : E2 + O2 = 3 * n2 := by
    dsimp only [E2, O2, n2]
    linarith only [hphi9_2, hphi9_5]
  have heven : E0 + E1 + E2 = 6 := by
    dsimp only [E0, E1, E2]
    linarith only [hmod4_0, hmod4_2]
  have hodd : O0 + O1 + O2 = 6 := by
    dsimp only [O0, O1, O2]
    linarith only [hmod4_1, hmod4_3]
  have hcphi0 : E0 - O0 - E2 + O2 = 5 * k0 := by
    dsimp only [E0, O0, E1, O1, E2, O2]
    linarith only [hphi6_0]
  have hcphi1 : -E1 + O1 + E2 - O2 = 5 * k1 := by
    dsimp only [E0, O0, E1, O1, E2, O2]
    linarith only [hphi6_1]
  exact z180_k12_m6_order9_compact_impossible
    E0 O0 E1 O1 E2 O2 n0 n1 n2 k0 k1
    hE0lo hE0hi hO0lo hO0hi hE1lo hE1hi hO1lo hO1hi
    hE2lo hE2hi hO2lo hO2hi hclass0 hclass1 hclass2
    heven hodd hcphi0 hcphi1 hphi6_ne

#print axioms z180_k12_m6_order9_compact_indicator_impossible

end Fuglede
