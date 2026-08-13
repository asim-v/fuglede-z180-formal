-- Raw report SHA-256: bb63f844137560f6532c1612492f63309f876a8079997dc2cc077389632d65bc
-- Sharder SHA-256: 176cfb7c976a1795539d84805650b69b7d68eec68db6b762f18664a6717af62a
import Fuglede.Z180K12M6Order9PairP1ZShard000
import Fuglede.Z180K12M6Order9PairP1ZShard001
import Fuglede.Z180K12M6Order9PairP1ZShard002
import Fuglede.Z180K12M6Order9PairP1ZShard003
import Fuglede.Z180K12M6Order9PairP1ZShard004
import Fuglede.Z180K12M6Order9PairP1ZShard005
import Fuglede.Z180K12M6Order9PairP1ZShard006
import Fuglede.Z180K12M6Order9PairP1ZShard007
import Fuglede.Z180K12M6Order9PairP1ZShard008
import Fuglede.Z180K12M6Order9PairP1ZShard009
import Fuglede.Z180K12M6Order9PairP1ZShard010
import Fuglede.Z180K12M6Order9PairP1ZShard011
import Fuglede.Z180K12M6Order9PairP1ZShard012
import Fuglede.Z180K12M6Order9PairP1ZShard013
import Fuglede.Z180K12M6Order9PairP1ZShard014
import Fuglede.Z180K12M6Order9PairP1ZShard015
import Fuglede.Z180K12M6Order9PairP1ZShard016
import Fuglede.Z180K12M6Order9PairP1ZShard017
import Fuglede.Z180K12M6Order9PairP1ZShard018
import Fuglede.Z180K12M6Order9PairP1ZShard019
import Fuglede.Z180K12M6Order9PairP1ZShard020
import Fuglede.Z180K12M6Order9PairP1ZShard021
import Fuglede.Z180K12M6Order9PairP1ZShard022
import Fuglede.Z180K12M6Order9PairP1ZShard023
import Fuglede.Z180K12M6Order9PairP1ZShard024
import Fuglede.Z180K12M6Order9PairP1ZShard025
import Fuglede.Z180K12M6Order9PairP1ZShard026
import Fuglede.Z180K12M6Order9PairP1ZShard027
import Fuglede.Z180K12M6Order9PairP1ZShard028
import Fuglede.Z180K12M6Order9PairP1ZShard029
import Fuglede.Z180K12M6Order9PairP1ZShard030
import Fuglede.Z180K12M6Order9PairP1ZShard031
import Fuglede.Z180K12M6Order9PairP1ZShard032
import Fuglede.Z180K12M6Order9PairP1ZShard033
import Fuglede.Z180K12M6Order9PairP1ZShard034
import Fuglede.Z180K12M6Order9PairP1ZShard035
import Fuglede.Z180K12M6Order9PairP1ZShard036
import Fuglede.Z180K12M6Order9PairP1ZShard037
import Fuglede.Z180K12M6Order9PairP1ZShard038
import Fuglede.Z180K12M6Order9PairP1ZShard039
import Fuglede.Z180K12M6Order9PairP1ZShard040
import Fuglede.Z180K12M6Order9PairP1ZShard041
import Fuglede.Z180K12M6Order9PairP1ZShard042
import Fuglede.Z180K12M6Order9PairP1ZShard043
import Fuglede.Z180K12M6Order9PairP1ZShard044
import Fuglede.Z180K12M6Order9PairP1ZShard045
import Fuglede.Z180K12M6Order9PairP1ZShard046
import Fuglede.Z180K12M6Order9PairP1ZShard047
import Fuglede.Z180K12M6Order9PairP1ZShard048
import Fuglede.Z180K12M6Order9PairP1ZShard049
import Fuglede.Z180K12M6Order9PairP1ZShard050
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Fuglede


theorem z180_k12_m6_order9_pair_p1_z_impossible
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
    (hphi6_0 : (((b_0 * 1) + (b_1 * 0) + (b_2 * (-1)) + (b_3 * (-1)) + (b_4 * 0) + (b_5 * 1) + (b_6 * 1) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * (-1)) + (b_10 * 0) + (b_11 * 1) + (b_12 * 1) + (b_13 * 0) + (b_14 * (-1)) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 1) + (b_18 * 1) + (b_19 * 0) + (b_20 * (-1)) + (b_21 * (-1)) + (b_22 * 0) + (b_23 * 1) + (b_24 * 1) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * (-1)) + (b_28 * 0) + (b_29 * 1) + (b_30 * 1) + (b_31 * 0) + (b_32 * (-1)) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 1)) = 5))
    (hphi6_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 1) + (b_3 * 0) + (b_4 * (-1)) + (b_5 * (-1)) + (b_6 * 0) + (b_7 * 1) + (b_8 * 1) + (b_9 * 0) + (b_10 * (-1)) + (b_11 * (-1)) + (b_12 * 0) + (b_13 * 1) + (b_14 * 1) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 1) + (b_20 * 1) + (b_21 * 0) + (b_22 * (-1)) + (b_23 * (-1)) + (b_24 * 0) + (b_25 * 1) + (b_26 * 1) + (b_27 * 0) + (b_28 * (-1)) + (b_29 * (-1)) + (b_30 * 0) + (b_31 * 1) + (b_32 * 1) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * (-1))) = 0))
    : False := by
  have c0 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
  rcases c0 with c0_low | c0_high
  · have c1 : b_11 ≤ 0 ∨ 1 ≤ b_11 := by omega
    rcases c1 with c1_low | c1_high
    · have c2 : b_19 ≤ 0 ∨ 1 ≤ b_19 := by omega
      rcases c2 with c2_low | c2_high
      · have c3 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
        rcases c3 with c3_low | c3_high
        · exact z180_k12_m6_order9_pair_p1_z_shard_000_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_low
        · have c4 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
          rcases c4 with c4_low | c4_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_001_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_low
          · have c21 : b_5 ≤ 0 ∨ 1 ≤ b_5 := by omega
            rcases c21 with c21_low | c21_high
            · have c22 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
              rcases c22 with c22_low | c22_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_002_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_high c21_low c22_low
              · exact z180_k12_m6_order9_pair_p1_z_shard_003_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_high c21_low c22_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_004_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_high c21_high
      · have c67 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
        rcases c67 with c67_low | c67_high
        · have c68 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
          rcases c68 with c68_low | c68_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_005_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_low c68_low
          · have c69 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
            rcases c69 with c69_low | c69_high
            · have c70 : b_17 ≤ 0 ∨ 1 ≤ b_17 := by omega
              rcases c70 with c70_low | c70_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_006_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_low c68_high c69_low c70_low
              · exact z180_k12_m6_order9_pair_p1_z_shard_007_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_low c68_high c69_low c70_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_008_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_low c68_high c69_high
        · have c114 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
          rcases c114 with c114_low | c114_high
          · have c115 : b_20 ≤ 0 ∨ 1 ≤ b_20 := by omega
            rcases c115 with c115_low | c115_high
            · have c116 : b_3 ≤ 0 ∨ 1 ≤ b_3 := by omega
              rcases c116 with c116_low | c116_high
              · have c117 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
                rcases c117 with c117_low | c117_high
                · have c118 : b_21 ≤ 0 ∨ 1 ≤ b_21 := by omega
                  rcases c118 with c118_low | c118_high
                  · have c119 : b_32 ≤ 0 ∨ 1 ≤ b_32 := by omega
                    rcases c119 with c119_low | c119_high
                    · have c120 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
                      rcases c120 with c120_low | c120_high
                      · have c121 : b_15 ≤ 0 ∨ 1 ≤ b_15 := by omega
                        rcases c121 with c121_low | c121_high
                        · exact z180_k12_m6_order9_pair_p1_z_shard_009_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_low c118_low c119_low c120_low c121_low
                        · exact z180_k12_m6_order9_pair_p1_z_shard_010_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_low c118_low c119_low c120_low c121_high
                      · exact z180_k12_m6_order9_pair_p1_z_shard_011_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_low c118_low c119_low c120_high
                    · exact z180_k12_m6_order9_pair_p1_z_shard_012_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_low c118_low c119_high
                  · exact z180_k12_m6_order9_pair_p1_z_shard_013_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_low c118_high
                · exact z180_k12_m6_order9_pair_p1_z_shard_014_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_low c117_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_015_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_low c116_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_016_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_low c115_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_017_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c67_high c114_high
    · have c199 : b_22 ≤ 0 ∨ 1 ≤ b_22 := by omega
      rcases c199 with c199_low | c199_high
      · have c200 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
        rcases c200 with c200_low | c200_high
        · have c201 : b_16 ≤ 0 ∨ 1 ≤ b_16 := by omega
          rcases c201 with c201_low | c201_high
          · have c202 : b_28 ≤ 0 ∨ 1 ≤ b_28 := by omega
            rcases c202 with c202_low | c202_high
            · have c203 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
              rcases c203 with c203_low | c203_high
              · have c204 : b_34 ≤ 0 ∨ 1 ≤ b_34 := by omega
                rcases c204 with c204_low | c204_high
                · exact z180_k12_m6_order9_pair_p1_z_shard_018_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_low c202_low c203_low c204_low
                · have c224 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
                  rcases c224 with c224_low | c224_high
                  · exact z180_k12_m6_order9_pair_p1_z_shard_019_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_low c202_low c203_low c204_high c224_low
                  · exact z180_k12_m6_order9_pair_p1_z_shard_020_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_low c202_low c203_low c204_high c224_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_021_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_low c202_low c203_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_022_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_low c202_high
          · have c276 : b_5 ≤ 0 ∨ 1 ≤ b_5 := by omega
            rcases c276 with c276_low | c276_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_023_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_high c276_low
            · exact z180_k12_m6_order9_pair_p1_z_shard_024_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_low c201_high c276_high
        · exact z180_k12_m6_order9_pair_p1_z_shard_025_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_low c200_high
      · exact z180_k12_m6_order9_pair_p1_z_shard_026_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c199_high
  · have c340 : b_22 ≤ 0 ∨ 1 ≤ b_22 := by omega
    rcases c340 with c340_low | c340_high
    · have c341 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
      rcases c341 with c341_low | c341_high
      · have c342 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
        rcases c342 with c342_low | c342_high
        · have c343 : b_28 ≤ 0 ∨ 1 ≤ b_28 := by omega
          rcases c343 with c343_low | c343_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_027_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_low
          · have c344 : b_5 ≤ 0 ∨ 1 ≤ b_5 := by omega
            rcases c344 with c344_low | c344_high
            · have c345 : b_11 ≤ 0 ∨ 1 ≤ b_11 := by omega
              rcases c345 with c345_low | c345_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_028_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_high c344_low c345_low
              · exact z180_k12_m6_order9_pair_p1_z_shard_029_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_high c344_low c345_high
            · have c377 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
              rcases c377 with c377_low | c377_high
              · have c378 : b_17 ≤ 0 ∨ 1 ≤ b_17 := by omega
                rcases c378 with c378_low | c378_high
                · exact z180_k12_m6_order9_pair_p1_z_shard_030_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_high c344_high c377_low c378_low
                · exact z180_k12_m6_order9_pair_p1_z_shard_031_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_high c344_high c377_low c378_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_032_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_low c343_high c344_high c377_high
        · have c410 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
          rcases c410 with c410_low | c410_high
          · have c411 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
            rcases c411 with c411_low | c411_high
            · have c412 : b_20 ≤ 0 ∨ 1 ≤ b_20 := by omega
              rcases c412 with c412_low | c412_high
              · have c413 : b_32 ≤ 0 ∨ 1 ≤ b_32 := by omega
                rcases c413 with c413_low | c413_high
                · exact z180_k12_m6_order9_pair_p1_z_shard_033_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_high c410_low c411_low c412_low c413_low
                · exact z180_k12_m6_order9_pair_p1_z_shard_034_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_high c410_low c411_low c412_low c413_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_035_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_high c410_low c411_low c412_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_036_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_high c410_low c411_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_037_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_low c342_high c410_high
      · have c468 : b_14 ≤ 0 ∨ 1 ≤ b_14 := by omega
        rcases c468 with c468_low | c468_high
        · have c469 : b_32 ≤ 0 ∨ 1 ≤ b_32 := by omega
          rcases c469 with c469_low | c469_high
          · have c470 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
            rcases c470 with c470_low | c470_high
            · have c471 : b_26 ≤ 0 ∨ 1 ≤ b_26 := by omega
              rcases c471 with c471_low | c471_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_038_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_high c468_low c469_low c470_low c471_low
              · exact z180_k12_m6_order9_pair_p1_z_shard_039_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_high c468_low c469_low c470_low c471_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_040_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_high c468_low c469_low c470_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_041_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_high c468_low c469_high
        · exact z180_k12_m6_order9_pair_p1_z_shard_042_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_low c341_high c468_high
    · have c530 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
      rcases c530 with c530_low | c530_high
      · exact z180_k12_m6_order9_pair_p1_z_shard_043_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_low
      · have c546 : b_27 ≤ 0 ∨ 1 ≤ b_27 := by omega
        rcases c546 with c546_low | c546_high
        · have c547 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
          rcases c547 with c547_low | c547_high
          · have c548 : b_33 ≤ 0 ∨ 1 ≤ b_33 := by omega
            rcases c548 with c548_low | c548_high
            · have c549 : b_15 ≤ 0 ∨ 1 ≤ b_15 := by omega
              rcases c549 with c549_low | c549_high
              · have c550 : b_17 ≤ 0 ∨ 1 ≤ b_17 := by omega
                rcases c550 with c550_low | c550_high
                · exact z180_k12_m6_order9_pair_p1_z_shard_044_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_low c548_low c549_low c550_low
                · have c572 : b_5 ≤ 0 ∨ 1 ≤ b_5 := by omega
                  rcases c572 with c572_low | c572_high
                  · exact z180_k12_m6_order9_pair_p1_z_shard_045_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_low c548_low c549_low c550_high c572_low
                  · exact z180_k12_m6_order9_pair_p1_z_shard_046_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_low c548_low c549_low c550_high c572_high
              · exact z180_k12_m6_order9_pair_p1_z_shard_047_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_low c548_low c549_high
            · exact z180_k12_m6_order9_pair_p1_z_shard_048_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_low c548_high
          · exact z180_k12_m6_order9_pair_p1_z_shard_049_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_low c547_high
        · exact z180_k12_m6_order9_pair_p1_z_shard_050_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c340_high c530_high c546_high

#print axioms z180_k12_m6_order9_pair_p1_z_impossible

end Fuglede
