-- Raw report SHA-256: bb63f844137560f6532c1612492f63309f876a8079997dc2cc077389632d65bc
-- Sharder SHA-256: 176cfb7c976a1795539d84805650b69b7d68eec68db6b762f18664a6717af62a
import Fuglede.Z180K12M6Order9PairP1M1Shard000
import Fuglede.Z180K12M6Order9PairP1M1Shard001
import Fuglede.Z180K12M6Order9PairP1M1Shard002
import Fuglede.Z180K12M6Order9PairP1M1Shard003
import Fuglede.Z180K12M6Order9PairP1M1Shard004
import Fuglede.Z180K12M6Order9PairP1M1Shard005
import Fuglede.Z180K12M6Order9PairP1M1Shard006
import Fuglede.Z180K12M6Order9PairP1M1Shard007
import Fuglede.Z180K12M6Order9PairP1M1Shard008
import Fuglede.Z180K12M6Order9PairP1M1Shard009
import Fuglede.Z180K12M6Order9PairP1M1Shard010
import Fuglede.Z180K12M6Order9PairP1M1Shard011
import Fuglede.Z180K12M6Order9PairP1M1Shard012
import Fuglede.Z180K12M6Order9PairP1M1Shard013
import Fuglede.Z180K12M6Order9PairP1M1Shard014
import Fuglede.Z180K12M6Order9PairP1M1Shard015
import Fuglede.Z180K12M6Order9PairP1M1Shard016
import Fuglede.Z180K12M6Order9PairP1M1Shard017
import Fuglede.Z180K12M6Order9PairP1M1Shard018
import Fuglede.Z180K12M6Order9PairP1M1Shard019
import Fuglede.Z180K12M6Order9PairP1M1Shard020
import Fuglede.Z180K12M6Order9PairP1M1Shard021
import Fuglede.Z180K12M6Order9PairP1M1Shard022
import Fuglede.Z180K12M6Order9PairP1M1Shard023
import Fuglede.Z180K12M6Order9PairP1M1Shard024
import Fuglede.Z180K12M6Order9PairP1M1Shard025
import Fuglede.Z180K12M6Order9PairP1M1Shard026
import Fuglede.Z180K12M6Order9PairP1M1Shard027
import Fuglede.Z180K12M6Order9PairP1M1Shard028
import Fuglede.Z180K12M6Order9PairP1M1Shard029
import Fuglede.Z180K12M6Order9PairP1M1Shard030
import Fuglede.Z180K12M6Order9PairP1M1Shard031
import Fuglede.Z180K12M6Order9PairP1M1Shard032
import Fuglede.Z180K12M6Order9PairP1M1Shard033
import Fuglede.Z180K12M6Order9PairP1M1Shard034
import Fuglede.Z180K12M6Order9PairP1M1Shard035
import Fuglede.Z180K12M6Order9PairP1M1Shard036
import Fuglede.Z180K12M6Order9PairP1M1Shard037
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Fuglede


theorem z180_k12_m6_order9_pair_p1_m1_impossible
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
    (hphi6_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 1) + (b_3 * 0) + (b_4 * (-1)) + (b_5 * (-1)) + (b_6 * 0) + (b_7 * 1) + (b_8 * 1) + (b_9 * 0) + (b_10 * (-1)) + (b_11 * (-1)) + (b_12 * 0) + (b_13 * 1) + (b_14 * 1) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 1) + (b_20 * 1) + (b_21 * 0) + (b_22 * (-1)) + (b_23 * (-1)) + (b_24 * 0) + (b_25 * 1) + (b_26 * 1) + (b_27 * 0) + (b_28 * (-1)) + (b_29 * (-1)) + (b_30 * 0) + (b_31 * 1) + (b_32 * 1) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * (-1))) = (-5)))
    : False := by
  have c0 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
  rcases c0 with c0_low | c0_high
  · have c1 : b_16 ≤ 0 ∨ 1 ≤ b_16 := by omega
    rcases c1 with c1_low | c1_high
    · have c2 : b_22 ≤ 0 ∨ 1 ≤ b_22 := by omega
      rcases c2 with c2_low | c2_high
      · have c3 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
        rcases c3 with c3_low | c3_high
        · exact z180_k12_m6_order9_pair_p1_m1_shard_000_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_low
        · have c4 : b_18 ≤ 0 ∨ 1 ≤ b_18 := by omega
          rcases c4 with c4_low | c4_high
          · have c5 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
            rcases c5 with c5_low | c5_high
            · have c6 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
              rcases c6 with c6_low | c6_high
              · exact z180_k12_m6_order9_pair_p1_m1_shard_001_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_low c5_low c6_low
              · have c7 : b_17 ≤ 0 ∨ 1 ≤ b_17 := by omega
                rcases c7 with c7_low | c7_high
                · exact z180_k12_m6_order9_pair_p1_m1_shard_002_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_low c5_low c6_high c7_low
                · exact z180_k12_m6_order9_pair_p1_m1_shard_003_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_low c5_low c6_high c7_high
            · exact z180_k12_m6_order9_pair_p1_m1_shard_004_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_low c5_high
          · exact z180_k12_m6_order9_pair_p1_m1_shard_005_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_low c3_high c4_high
      · have c51 : b_21 ≤ 0 ∨ 1 ≤ b_21 := by omega
        rcases c51 with c51_low | c51_high
        · have c52 : b_3 ≤ 0 ∨ 1 ≤ b_3 := by omega
          rcases c52 with c52_low | c52_high
          · have c53 : b_27 ≤ 0 ∨ 1 ≤ b_27 := by omega
            rcases c53 with c53_low | c53_high
            · have c54 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
              rcases c54 with c54_low | c54_high
              · have c55 : b_33 ≤ 0 ∨ 1 ≤ b_33 := by omega
                rcases c55 with c55_low | c55_high
                · have c56 : b_15 ≤ 0 ∨ 1 ≤ b_15 := by omega
                  rcases c56 with c56_low | c56_high
                  · exact z180_k12_m6_order9_pair_p1_m1_shard_006_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low c53_low c54_low c55_low c56_low
                  · exact z180_k12_m6_order9_pair_p1_m1_shard_007_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low c53_low c54_low c55_low c56_high
                · exact z180_k12_m6_order9_pair_p1_m1_shard_008_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low c53_low c54_low c55_high
              · exact z180_k12_m6_order9_pair_p1_m1_shard_009_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low c53_low c54_high
            · exact z180_k12_m6_order9_pair_p1_m1_shard_010_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_low c53_high
          · exact z180_k12_m6_order9_pair_p1_m1_shard_011_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_low c52_high
        · exact z180_k12_m6_order9_pair_p1_m1_shard_012_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_low c2_high c51_high
    · have c132 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
      rcases c132 with c132_low | c132_high
      · have c133 : b_17 ≤ 0 ∨ 1 ≤ b_17 := by omega
        rcases c133 with c133_low | c133_high
        · have c134 : b_19 ≤ 0 ∨ 1 ≤ b_19 := by omega
          rcases c134 with c134_low | c134_high
          · exact z180_k12_m6_order9_pair_p1_m1_shard_013_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_low c134_low
          · exact z180_k12_m6_order9_pair_p1_m1_shard_014_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_low c134_high
        · have c168 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
          rcases c168 with c168_low | c168_high
          · have c169 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
            rcases c169 with c169_low | c169_high
            · exact z180_k12_m6_order9_pair_p1_m1_shard_015_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_high c168_low c169_low
            · have c196 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
              rcases c196 with c196_low | c196_high
              · have c197 : b_3 ≤ 0 ∨ 1 ≤ b_3 := by omega
                rcases c197 with c197_low | c197_high
                · exact z180_k12_m6_order9_pair_p1_m1_shard_016_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_high c168_low c169_high c196_low c197_low
                · exact z180_k12_m6_order9_pair_p1_m1_shard_017_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_high c168_low c169_high c196_low c197_high
              · exact z180_k12_m6_order9_pair_p1_m1_shard_018_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_high c168_low c169_high c196_high
          · exact z180_k12_m6_order9_pair_p1_m1_shard_019_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_low c133_high c168_high
      · have c253 : b_27 ≤ 0 ∨ 1 ≤ b_27 := by omega
        rcases c253 with c253_low | c253_high
        · have c254 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
          rcases c254 with c254_low | c254_high
          · exact z180_k12_m6_order9_pair_p1_m1_shard_020_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_high c253_low c254_low
          · exact z180_k12_m6_order9_pair_p1_m1_shard_021_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_high c253_low c254_high
        · exact z180_k12_m6_order9_pair_p1_m1_shard_022_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_low c1_high c132_high c253_high
  · have c298 : b_27 ≤ 0 ∨ 1 ≤ b_27 := by omega
    rcases c298 with c298_low | c298_high
    · have c299 : b_3 ≤ 0 ∨ 1 ≤ b_3 := by omega
      rcases c299 with c299_low | c299_high
      · have c300 : b_21 ≤ 0 ∨ 1 ≤ b_21 := by omega
        rcases c300 with c300_low | c300_high
        · have c301 : b_30 ≤ 0 ∨ 1 ≤ b_30 := by omega
          rcases c301 with c301_low | c301_high
          · have c302 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
            rcases c302 with c302_low | c302_high
            · have c303 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
              rcases c303 with c303_low | c303_high
              · have c304 : b_25 ≤ 0 ∨ 1 ≤ b_25 := by omega
                rcases c304 with c304_low | c304_high
                · exact z180_k12_m6_order9_pair_p1_m1_shard_023_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_low c304_low
                · have c322 : b_15 ≤ 0 ∨ 1 ≤ b_15 := by omega
                  rcases c322 with c322_low | c322_high
                  · have c323 : b_19 ≤ 0 ∨ 1 ≤ b_19 := by omega
                    rcases c323 with c323_low | c323_high
                    · have c324 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
                      rcases c324 with c324_low | c324_high
                      · exact z180_k12_m6_order9_pair_p1_m1_shard_024_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_low c304_high c322_low c323_low c324_low
                      · exact z180_k12_m6_order9_pair_p1_m1_shard_025_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_low c304_high c322_low c323_low c324_high
                    · exact z180_k12_m6_order9_pair_p1_m1_shard_026_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_low c304_high c322_low c323_high
                  · exact z180_k12_m6_order9_pair_p1_m1_shard_027_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_low c304_high c322_high
              · exact z180_k12_m6_order9_pair_p1_m1_shard_028_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_low c303_high
            · exact z180_k12_m6_order9_pair_p1_m1_shard_029_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_low c302_high
          · have c363 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
            rcases c363 with c363_low | c363_high
            · have c364 : b_25 ≤ 0 ∨ 1 ≤ b_25 := by omega
              rcases c364 with c364_low | c364_high
              · exact z180_k12_m6_order9_pair_p1_m1_shard_030_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_high c363_low c364_low
              · exact z180_k12_m6_order9_pair_p1_m1_shard_031_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_high c363_low c364_high
            · exact z180_k12_m6_order9_pair_p1_m1_shard_032_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_low c301_high c363_high
        · exact z180_k12_m6_order9_pair_p1_m1_shard_033_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_low c300_high
      · exact z180_k12_m6_order9_pair_p1_m1_shard_034_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_low c299_high
    · have c452 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
      rcases c452 with c452_low | c452_high
      · have c453 : b_31 ≤ 0 ∨ 1 ≤ b_31 := by omega
        rcases c453 with c453_low | c453_high
        · exact z180_k12_m6_order9_pair_p1_m1_shard_035_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_high c452_low c453_low
        · exact z180_k12_m6_order9_pair_p1_m1_shard_036_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_high c452_low c453_high
      · exact z180_k12_m6_order9_pair_p1_m1_shard_037_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi9_0 hphi9_1 hphi9_2 hphi9_3 hphi9_4 hphi9_5 hphi6_0 hphi6_1 c0_high c298_high c452_high

#print axioms z180_k12_m6_order9_pair_p1_m1_impossible

end Fuglede
