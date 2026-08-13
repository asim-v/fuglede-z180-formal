-- Raw report SHA-256: bb63f844137560f6532c1612492f63309f876a8079997dc2cc077389632d65bc
-- Sharder SHA-256: 176cfb7c976a1795539d84805650b69b7d68eec68db6b762f18664a6717af62a
import Fuglede.Z180K12M6Order9PairZM1Shard000
import Fuglede.Z180K12M6Order9PairZM1Shard001
import Fuglede.Z180K12M6Order9PairZM1Shard002
import Fuglede.Z180K12M6Order9PairZM1Shard003
import Fuglede.Z180K12M6Order9PairZM1Shard004
import Fuglede.Z180K12M6Order9PairZM1Shard005
import Fuglede.Z180K12M6Order9PairZM1Shard006
import Fuglede.Z180K12M6Order9PairZM1Shard007
import Fuglede.Z180K12M6Order9PairZM1Shard008
import Fuglede.Z180K12M6Order9PairZM1Shard009
import Fuglede.Z180K12M6Order9PairZM1Shard010
import Fuglede.Z180K12M6Order9PairZM1Shard011
import Fuglede.Z180K12M6Order9PairZM1Shard012
import Fuglede.Z180K12M6Order9PairZM1Shard013
import Fuglede.Z180K12M6Order9PairZM1Shard014
import Fuglede.Z180K12M6Order9PairZM1Shard015
import Fuglede.Z180K12M6Order9PairZM1Shard016
import Fuglede.Z180K12M6Order9PairZM1Shard017
import Fuglede.Z180K12M6Order9PairZM1Shard018
import Fuglede.Z180K12M6Order9PairZM1Shard019
import Fuglede.Z180K12M6Order9PairZM1Shard020
import Fuglede.Z180K12M6Order9PairZM1Shard021
import Fuglede.Z180K12M6Order9PairZM1Shard022
import Fuglede.Z180K12M6Order9PairZM1Shard023
import Fuglede.Z180K12M6Order9PairZM1Shard024
import Fuglede.Z180K12M6Order9PairZM1Shard025
import Fuglede.Z180K12M6Order9PairZM1Shard026
import Fuglede.Z180K12M6Order9PairZM1Shard027
import Fuglede.Z180K12M6Order9PairZM1Shard028
import Fuglede.Z180K12M6Order9PairZM1Shard029
import Fuglede.Z180K12M6Order9PairZM1Shard030
import Fuglede.Z180K12M6Order9PairZM1Shard031
import Fuglede.Z180K12M6Order9PairZM1Shard032
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Fuglede


theorem z180_k12_m6_order9_pair_z_m1_impossible
    (b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 : Int)
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
    (hphi6_0 : (((b_0 * 1) + (b_1 * 0) + (b_2 * (-1)) + (b_3 * (-1)) + (b_4 * 0) + (b_5 * 1) + (b_6 * 1) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * (-1)) + (b_10 * 0) + (b_11 * 1) + (b_12 * 1) + (b_13 * 0) + (b_14 * (-1)) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 1) + (b_18 * 1) + (b_19 * 0) + (b_20 * (-1)) + (b_21 * (-1)) + (b_22 * 0) + (b_23 * 1) + (b_24 * 1) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * (-1)) + (b_28 * 0) + (b_29 * 1) + (b_30 * 1) + (b_31 * 0) + (b_32 * (-1)) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 1)) = 0))
    (hphi6_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 1) + (b_3 * 0) + (b_4 * (-1)) + (b_5 * (-1)) + (b_6 * 0) + (b_7 * 1) + (b_8 * 1) + (b_9 * 0) + (b_10 * (-1)) + (b_11 * (-1)) + (b_12 * 0) + (b_13 * 1) + (b_14 * 1) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 1) + (b_20 * 1) + (b_21 * 0) + (b_22 * (-1)) + (b_23 * (-1)) + (b_24 * 0) + (b_25 * 1) + (b_26 * 1) + (b_27 * 0) + (b_28 * (-1)) + (b_29 * (-1)) + (b_30 * 0) + (b_31 * 1) + (b_32 * 1) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * (-1))) = (-5)))
    : False := by
  have c0 : b_11 ≤ 0 ∨ 1 ≤ b_11 := by omega
  rcases c0 with c0_low | c0_high
  · have c1 : b_3 ≤ 0 ∨ 1 ≤ b_3 := by omega
    rcases c1 with c1_low | c1_high
    · have c2 : b_23 ≤ 0 ∨ 1 ≤ b_23 := by omega
      rcases c2 with c2_low | c2_high
      · have c3 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
        rcases c3 with c3_low | c3_high
        · have c4 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
          rcases c4 with c4_low | c4_high
          · have c5 : b_32 ≤ 0 ∨ 1 ≤ b_32 := by omega
            rcases c5 with c5_low | c5_high
            · exact z180_k12_m6_order9_pair_z_m1_shard_000_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_low c4_low c5_low
            · exact z180_k12_m6_order9_pair_z_m1_shard_001_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_low c4_low c5_high
          · exact z180_k12_m6_order9_pair_z_m1_shard_002_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_low c4_high
        · exact z180_k12_m6_order9_pair_z_m1_shard_003_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high
      · have c51 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
        rcases c51 with c51_low | c51_high
        · have c52 : b_20 ≤ 0 ∨ 1 ≤ b_20 := by omega
          rcases c52 with c52_low | c52_high
          · exact z180_k12_m6_order9_pair_z_m1_shard_004_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low
          · have c55 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
            rcases c55 with c55_low | c55_high
            · have c56 : b_24 ≤ 0 ∨ 1 ≤ b_24 := by omega
              rcases c56 with c56_low | c56_high
              · have c57 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
                rcases c57 with c57_low | c57_high
                · have c58 : b_18 ≤ 0 ∨ 1 ≤ b_18 := by omega
                  rcases c58 with c58_low | c58_high
                  · have c59 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
                    rcases c59 with c59_low | c59_high
                    · exact z180_k12_m6_order9_pair_z_m1_shard_005_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_low c56_low c57_low c58_low c59_low
                    · exact z180_k12_m6_order9_pair_z_m1_shard_006_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_low c56_low c57_low c58_low c59_high
                  · exact z180_k12_m6_order9_pair_z_m1_shard_007_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_low c56_low c57_low c58_high
                · exact z180_k12_m6_order9_pair_z_m1_shard_008_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_low c56_low c57_high
              · exact z180_k12_m6_order9_pair_z_m1_shard_009_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_low c56_high
            · exact z180_k12_m6_order9_pair_z_m1_shard_010_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high c55_high
        · have c101 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
          rcases c101 with c101_low | c101_high
          · have c102 : b_27 ≤ 0 ∨ 1 ≤ b_27 := by omega
            rcases c102 with c102_low | c102_high
            · exact z180_k12_m6_order9_pair_z_m1_shard_011_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_high c101_low c102_low
            · exact z180_k12_m6_order9_pair_z_m1_shard_012_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_high c101_low c102_high
          · exact z180_k12_m6_order9_pair_z_m1_shard_013_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_high c101_high
    · have c136 : b_26 ≤ 0 ∨ 1 ≤ b_26 := by omega
      rcases c136 with c136_low | c136_high
      · have c137 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
        rcases c137 with c137_low | c137_high
        · have c138 : b_32 ≤ 0 ∨ 1 ≤ b_32 := by omega
          rcases c138 with c138_low | c138_high
          · have c139 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
            rcases c139 with c139_low | c139_high
            · have c140 : b_20 ≤ 0 ∨ 1 ≤ b_20 := by omega
              rcases c140 with c140_low | c140_high
              · have c141 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
                rcases c141 with c141_low | c141_high
                · have c142 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
                  rcases c142 with c142_low | c142_high
                  · have c143 : b_13 ≤ 0 ∨ 1 ≤ b_13 := by omega
                    rcases c143 with c143_low | c143_high
                    · have c144 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
                      rcases c144 with c144_low | c144_high
                      · exact z180_k12_m6_order9_pair_z_m1_shard_014_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_low c142_low c143_low c144_low
                      · exact z180_k12_m6_order9_pair_z_m1_shard_015_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_low c142_low c143_low c144_high
                    · exact z180_k12_m6_order9_pair_z_m1_shard_016_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_low c142_low c143_high
                  · exact z180_k12_m6_order9_pair_z_m1_shard_017_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_low c142_high
                · have c206 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
                  rcases c206 with c206_low | c206_high
                  · exact z180_k12_m6_order9_pair_z_m1_shard_018_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_high c206_low
                  · exact z180_k12_m6_order9_pair_z_m1_shard_019_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_low c141_high c206_high
              · have c243 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
                rcases c243 with c243_low | c243_high
                · have c244 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
                  rcases c244 with c244_low | c244_high
                  · exact z180_k12_m6_order9_pair_z_m1_shard_020_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_high c243_low c244_low
                  · exact z180_k12_m6_order9_pair_z_m1_shard_021_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_high c243_low c244_high
                · exact z180_k12_m6_order9_pair_z_m1_shard_022_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_low c140_high c243_high
            · exact z180_k12_m6_order9_pair_z_m1_shard_023_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_low c139_high
          · exact z180_k12_m6_order9_pair_z_m1_shard_024_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_low c138_high
        · exact z180_k12_m6_order9_pair_z_m1_shard_025_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_low c137_high
      · exact z180_k12_m6_order9_pair_z_m1_shard_026_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c136_high
  · have c331 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
    rcases c331 with c331_low | c331_high
    · have c332 : b_20 ≤ 0 ∨ 1 ≤ b_20 := by omega
      rcases c332 with c332_low | c332_high
      · have c333 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
        rcases c333 with c333_low | c333_high
        · exact z180_k12_m6_order9_pair_z_m1_shard_027_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_low c332_low c333_low
        · have c363 : b_18 ≤ 0 ∨ 1 ≤ b_18 := by omega
          rcases c363 with c363_low | c363_high
          · have c364 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
            rcases c364 with c364_low | c364_high
            · exact z180_k12_m6_order9_pair_z_m1_shard_028_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_low c332_low c333_high c363_low c364_low
            · exact z180_k12_m6_order9_pair_z_m1_shard_029_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_low c332_low c333_high c363_low c364_high
          · exact z180_k12_m6_order9_pair_z_m1_shard_030_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_low c332_low c333_high c363_high
      · exact z180_k12_m6_order9_pair_z_m1_shard_031_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_low c332_high
    · exact z180_k12_m6_order9_pair_z_m1_shard_032_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c331_high

#print axioms z180_k12_m6_order9_pair_z_m1_impossible

end Fuglede
