-- Raw report SHA-256: 01f588aac602a8a69af9ac331e1e4600f5c9bb09b6e61f7fefefa07b207f61c2
-- Sharder SHA-256: 176cfb7c976a1795539d84805650b69b7d68eec68db6b762f18664a6717af62a
import Fuglede.Z180K12M6Order18PairP1ZShard000
import Fuglede.Z180K12M6Order18PairP1ZShard001
import Fuglede.Z180K12M6Order18PairP1ZShard002
import Fuglede.Z180K12M6Order18PairP1ZShard003
import Fuglede.Z180K12M6Order18PairP1ZShard004
import Fuglede.Z180K12M6Order18PairP1ZShard005
import Fuglede.Z180K12M6Order18PairP1ZShard006
import Fuglede.Z180K12M6Order18PairP1ZShard007
import Fuglede.Z180K12M6Order18PairP1ZShard008
import Fuglede.Z180K12M6Order18PairP1ZShard009
import Fuglede.Z180K12M6Order18PairP1ZShard010
import Fuglede.Z180K12M6Order18PairP1ZShard011
import Fuglede.Z180K12M6Order18PairP1ZShard012
import Fuglede.Z180K12M6Order18PairP1ZShard013
import Fuglede.Z180K12M6Order18PairP1ZShard014
import Fuglede.Z180K12M6Order18PairP1ZShard015
import Fuglede.Z180K12M6Order18PairP1ZShard016
import Fuglede.Z180K12M6Order18PairP1ZShard017
import Fuglede.Z180K12M6Order18PairP1ZShard018
import Fuglede.Z180K12M6Order18PairP1ZShard019
import Fuglede.Z180K12M6Order18PairP1ZShard020
import Fuglede.Z180K12M6Order18PairP1ZShard021
import Fuglede.Z180K12M6Order18PairP1ZShard022
import Fuglede.Z180K12M6Order18PairP1ZShard023
import Fuglede.Z180K12M6Order18PairP1ZShard024
import Fuglede.Z180K12M6Order18PairP1ZShard025
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Fuglede


theorem z180_k12_m6_order18_pair_p1_z_impossible
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
    (hphi18_0 : (((b_0 * 1) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * (-1)) + (b_7 * 0) + (b_8 * 0) + (b_9 * (-1)) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * 1) + (b_16 * 0) + (b_17 * 0) + (b_18 * 1) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * (-1)) + (b_25 * 0) + (b_26 * 0) + (b_27 * (-1)) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * 1) + (b_34 * 0) + (b_35 * 0)) = 0))
    (hphi18_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * 0) + (b_7 * (-1)) + (b_8 * 0) + (b_9 * 0) + (b_10 * (-1)) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * 0) + (b_16 * 1) + (b_17 * 0) + (b_18 * 0) + (b_19 * 1) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * 0) + (b_25 * (-1)) + (b_26 * 0) + (b_27 * 0) + (b_28 * (-1)) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * 0) + (b_34 * 1) + (b_35 * 0)) = 0))
    (hphi18_2 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 1) + (b_3 * 0) + (b_4 * 0) + (b_5 * 0) + (b_6 * 0) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * 0) + (b_10 * 0) + (b_11 * (-1)) + (b_12 * 0) + (b_13 * 0) + (b_14 * 0) + (b_15 * 0) + (b_16 * 0) + (b_17 * 1) + (b_18 * 0) + (b_19 * 0) + (b_20 * 1) + (b_21 * 0) + (b_22 * 0) + (b_23 * 0) + (b_24 * 0) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * 0) + (b_28 * 0) + (b_29 * (-1)) + (b_30 * 0) + (b_31 * 0) + (b_32 * 0) + (b_33 * 0) + (b_34 * 0) + (b_35 * 1)) = 0))
    (hphi18_3 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 1) + (b_4 * 0) + (b_5 * 0) + (b_6 * 1) + (b_7 * 0) + (b_8 * 0) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * (-1)) + (b_13 * 0) + (b_14 * 0) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 0) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 1) + (b_22 * 0) + (b_23 * 0) + (b_24 * 1) + (b_25 * 0) + (b_26 * 0) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * (-1)) + (b_31 * 0) + (b_32 * 0) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 0)) = 0))
    (hphi18_4 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 1) + (b_5 * 0) + (b_6 * 0) + (b_7 * 1) + (b_8 * 0) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * (-1)) + (b_14 * 0) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * 0) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 1) + (b_23 * 0) + (b_24 * 0) + (b_25 * 1) + (b_26 * 0) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * (-1)) + (b_32 * 0) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * 0)) = 0))
    (hphi18_5 : (((b_0 * 0) + (b_1 * 0) + (b_2 * 0) + (b_3 * 0) + (b_4 * 0) + (b_5 * 1) + (b_6 * 0) + (b_7 * 0) + (b_8 * 1) + (b_9 * 0) + (b_10 * 0) + (b_11 * 0) + (b_12 * 0) + (b_13 * 0) + (b_14 * (-1)) + (b_15 * 0) + (b_16 * 0) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 0) + (b_20 * 0) + (b_21 * 0) + (b_22 * 0) + (b_23 * 1) + (b_24 * 0) + (b_25 * 0) + (b_26 * 1) + (b_27 * 0) + (b_28 * 0) + (b_29 * 0) + (b_30 * 0) + (b_31 * 0) + (b_32 * (-1)) + (b_33 * 0) + (b_34 * 0) + (b_35 * (-1))) = 0))
    (hphi6_0 : (((b_0 * 1) + (b_1 * 0) + (b_2 * (-1)) + (b_3 * (-1)) + (b_4 * 0) + (b_5 * 1) + (b_6 * 1) + (b_7 * 0) + (b_8 * (-1)) + (b_9 * (-1)) + (b_10 * 0) + (b_11 * 1) + (b_12 * 1) + (b_13 * 0) + (b_14 * (-1)) + (b_15 * (-1)) + (b_16 * 0) + (b_17 * 1) + (b_18 * 1) + (b_19 * 0) + (b_20 * (-1)) + (b_21 * (-1)) + (b_22 * 0) + (b_23 * 1) + (b_24 * 1) + (b_25 * 0) + (b_26 * (-1)) + (b_27 * (-1)) + (b_28 * 0) + (b_29 * 1) + (b_30 * 1) + (b_31 * 0) + (b_32 * (-1)) + (b_33 * (-1)) + (b_34 * 0) + (b_35 * 1)) = 5))
    (hphi6_1 : (((b_0 * 0) + (b_1 * 1) + (b_2 * 1) + (b_3 * 0) + (b_4 * (-1)) + (b_5 * (-1)) + (b_6 * 0) + (b_7 * 1) + (b_8 * 1) + (b_9 * 0) + (b_10 * (-1)) + (b_11 * (-1)) + (b_12 * 0) + (b_13 * 1) + (b_14 * 1) + (b_15 * 0) + (b_16 * (-1)) + (b_17 * (-1)) + (b_18 * 0) + (b_19 * 1) + (b_20 * 1) + (b_21 * 0) + (b_22 * (-1)) + (b_23 * (-1)) + (b_24 * 0) + (b_25 * 1) + (b_26 * 1) + (b_27 * 0) + (b_28 * (-1)) + (b_29 * (-1)) + (b_30 * 0) + (b_31 * 1) + (b_32 * 1) + (b_33 * 0) + (b_34 * (-1)) + (b_35 * (-1))) = 0))
    : False := by
  have c0 : b_5 ≤ 0 ∨ 1 ≤ b_5 := by omega
  rcases c0 with c0_low | c0_high
  · have c1 : b_6 ≤ 0 ∨ 1 ≤ b_6 := by omega
    rcases c1 with c1_low | c1_high
    · exact z180_k12_m6_order18_pair_p1_z_shard_000_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_low
    · have c2 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
      rcases c2 with c2_low | c2_high
      · exact z180_k12_m6_order18_pair_p1_z_shard_001_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_low
      · have c3 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
        rcases c3 with c3_low | c3_high
        · have c4 : b_12 ≤ 0 ∨ 1 ≤ b_12 := by omega
          rcases c4 with c4_low | c4_high
          · exact z180_k12_m6_order18_pair_p1_z_shard_002_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_low c4_low
          · have c5 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
            rcases c5 with c5_low | c5_high
            · have c6 : b_13 ≤ 0 ∨ 1 ≤ b_13 := by omega
              rcases c6 with c6_low | c6_high
              · exact z180_k12_m6_order18_pair_p1_z_shard_003_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_low c4_high c5_low c6_low
              · have c36 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
                rcases c36 with c36_low | c36_high
                · exact z180_k12_m6_order18_pair_p1_z_shard_004_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_low c4_high c5_low c6_high c36_low
                · exact z180_k12_m6_order18_pair_p1_z_shard_005_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_low c4_high c5_low c6_high c36_high
            · exact z180_k12_m6_order18_pair_p1_z_shard_006_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_low c4_high c5_high
        · have c67 : b_11 ≤ 0 ∨ 1 ≤ b_11 := by omega
          rcases c67 with c67_low | c67_high
          · have c68 : b_16 ≤ 0 ∨ 1 ≤ b_16 := by omega
            rcases c68 with c68_low | c68_high
            · have c69 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
              rcases c69 with c69_low | c69_high
              · have c70 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
                rcases c70 with c70_low | c70_high
                · exact z180_k12_m6_order18_pair_p1_z_shard_007_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_high c67_low c68_low c69_low c70_low
                · exact z180_k12_m6_order18_pair_p1_z_shard_008_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_high c67_low c68_low c69_low c70_high
              · exact z180_k12_m6_order18_pair_p1_z_shard_009_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_high c67_low c68_low c69_high
            · exact z180_k12_m6_order18_pair_p1_z_shard_010_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_high c67_low c68_high
          · exact z180_k12_m6_order18_pair_p1_z_shard_011_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_low c1_high c2_high c3_high c67_high
  · have c130 : b_2 ≤ 0 ∨ 1 ≤ b_2 := by omega
    rcases c130 with c130_low | c130_high
    · have c131 : b_8 ≤ 0 ∨ 1 ≤ b_8 := by omega
      rcases c131 with c131_low | c131_high
      · have c132 : b_10 ≤ 0 ∨ 1 ≤ b_10 := by omega
        rcases c132 with c132_low | c132_high
        · have c133 : b_1 ≤ 0 ∨ 1 ≤ b_1 := by omega
          rcases c133 with c133_low | c133_high
          · have c134 : b_13 ≤ 0 ∨ 1 ≤ b_13 := by omega
            rcases c134 with c134_low | c134_high
            · have c135 : b_9 ≤ 0 ∨ 1 ≤ b_9 := by omega
              rcases c135 with c135_low | c135_high
              · have c136 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
                rcases c136 with c136_low | c136_high
                · exact z180_k12_m6_order18_pair_p1_z_shard_012_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_low c135_low c136_low
                · exact z180_k12_m6_order18_pair_p1_z_shard_013_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_low c135_low c136_high
              · exact z180_k12_m6_order18_pair_p1_z_shard_014_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_low c135_high
            · have c166 : b_0 ≤ 0 ∨ 1 ≤ b_0 := by omega
              rcases c166 with c166_low | c166_high
              · exact z180_k12_m6_order18_pair_p1_z_shard_015_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_high c166_low
              · have c167 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
                rcases c167 with c167_low | c167_high
                · exact z180_k12_m6_order18_pair_p1_z_shard_016_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_high c166_high c167_low
                · exact z180_k12_m6_order18_pair_p1_z_shard_017_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_low c134_high c166_high c167_high
          · have c198 : b_13 ≤ 0 ∨ 1 ≤ b_13 := by omega
            rcases c198 with c198_low | c198_high
            · have c199 : b_4 ≤ 0 ∨ 1 ≤ b_4 := by omega
              rcases c199 with c199_low | c199_high
              · have c200 : b_16 ≤ 0 ∨ 1 ≤ b_16 := by omega
                rcases c200 with c200_low | c200_high
                · exact z180_k12_m6_order18_pair_p1_z_shard_018_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_high c198_low c199_low c200_low
                · exact z180_k12_m6_order18_pair_p1_z_shard_019_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_high c198_low c199_low c200_high
              · exact z180_k12_m6_order18_pair_p1_z_shard_020_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_high c198_low c199_high
            · exact z180_k12_m6_order18_pair_p1_z_shard_021_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_low c133_high c198_high
        · exact z180_k12_m6_order18_pair_p1_z_shard_022_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_low c132_high
      · exact z180_k12_m6_order18_pair_p1_z_shard_023_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_low c131_high
    · have c268 : b_7 ≤ 0 ∨ 1 ≤ b_7 := by omega
      rcases c268 with c268_low | c268_high
      · exact z180_k12_m6_order18_pair_p1_z_shard_024_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_high c268_low
      · exact z180_k12_m6_order18_pair_p1_z_shard_025_impossible b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14 b_15 b_16 b_17 b_18 b_19 b_20 b_21 b_22 b_23 b_24 b_25 b_26 b_27 b_28 b_29 b_30 b_31 b_32 b_33 b_34 b_35 hlo_0 hhi_0 hlo_1 hhi_1 hlo_2 hhi_2 hlo_3 hhi_3 hlo_4 hhi_4 hlo_5 hhi_5 hlo_6 hhi_6 hlo_7 hhi_7 hlo_8 hhi_8 hlo_9 hhi_9 hlo_10 hhi_10 hlo_11 hhi_11 hlo_12 hhi_12 hlo_13 hhi_13 hlo_14 hhi_14 hlo_15 hhi_15 hlo_16 hhi_16 hlo_17 hhi_17 hlo_18 hhi_18 hlo_19 hhi_19 hlo_20 hhi_20 hlo_21 hhi_21 hlo_22 hhi_22 hlo_23 hhi_23 hlo_24 hhi_24 hlo_25 hhi_25 hlo_26 hhi_26 hlo_27 hhi_27 hlo_28 hhi_28 hlo_29 hhi_29 hlo_30 hhi_30 hlo_31 hhi_31 hlo_32 hhi_32 hlo_33 hhi_33 hlo_34 hhi_34 hlo_35 hhi_35 hmod4_0 hmod4_1 hmod4_2 hmod4_3 hphi18_0 hphi18_1 hphi18_2 hphi18_3 hphi18_4 hphi18_5 hphi6_0 hphi6_1 c0_high c130_high c268_high

#print axioms z180_k12_m6_order18_pair_p1_z_impossible

end Fuglede
