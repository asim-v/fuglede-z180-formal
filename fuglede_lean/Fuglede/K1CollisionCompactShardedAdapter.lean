import Fuglede.K1CollisionCompactPremises0
import Fuglede.K1CollisionCompactPremises1
import Fuglede.K1CollisionCompactPremises2
import Fuglede.K1CollisionCompactPremises3
import Fuglede.K1CollisionCompactPremises4
import Fuglede.K1CollisionCompactPremises5
import Fuglede.K1CollisionCompactPremises6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Sharded compact collision adapter for pinned k=1.
SMT SHA-256: `89b3e0fa4644c71bcca195f1964ffb4dddcf4910b0debda71dfa93237b4b8699`.
Core-index SHA-256: `ddda8c7134e39af7bcffc0f381cfd2c774df6f03d06ce5bab77c74b250b5a648`.
-/

namespace Fuglede

def K1CollisionCompactShardedRawCertificate : Prop :=
  ∀ (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop),
    -- core premise 0; source assertion 222
    ((a 0 1) = 0) →
    -- core premise 1; source assertion 224
    ((a 0 2) = 0) →
    -- core premise 2; source assertion 226
    ((a 0 4) = 0) →
    -- core premise 3; source assertion 228
    ((a 0 8) = 0) →
    -- core premise 4; source assertion 230
    ((a 0 16) = 0) →
    -- core premise 5; source assertion 663
    (¬ (z 1 1)) →
    -- core premise 6; source assertion 665
    (¬ (z 1 2)) →
    -- core premise 7; source assertion 667
    (¬ (z 1 4)) →
    -- core premise 8; source assertion 669
    (¬ (z 1 8)) →
    -- core premise 9; source assertion 704
    (((z 1 3)) → (z 1 1)) →
    -- core premise 10; source assertion 705
    (((z 1 5)) → (z 1 1)) →
    -- core premise 11; source assertion 707
    (((z 1 9)) → (z 1 1)) →
    -- core premise 12; source assertion 711
    (((z 1 17)) → (z 1 1)) →
    -- core premise 13; source assertion 720
    (((z 1 6)) → (z 1 2)) →
    -- core premise 14; source assertion 722
    (((z 1 10)) → (z 1 2)) →
    -- core premise 15; source assertion 726
    (((z 1 18)) → (z 1 2)) →
    -- core premise 16; source assertion 734
    (((z 1 7)) → (z 1 3)) →
    -- core premise 17; source assertion 735
    (((z 1 11)) → (z 1 3)) →
    -- core premise 18; source assertion 737
    (((z 1 19)) → (z 1 3)) →
    -- core premise 19; source assertion 744
    (((z 1 12)) → (z 1 4)) →
    -- core premise 20; source assertion 748
    (((z 1 20)) → (z 1 4)) →
    -- core premise 21; source assertion 757
    (((z 1 13)) → (z 1 5)) →
    -- core premise 22; source assertion 759
    (((z 1 21)) → (z 1 5)) →
    -- core premise 23; source assertion 764
    (((z 1 14)) → (z 1 6)) →
    -- core premise 24; source assertion 766
    (((z 1 22)) → (z 1 6)) →
    -- core premise 25; source assertion 770
    (((z 1 15)) → (z 1 7)) →
    -- core premise 26; source assertion 771
    (((z 1 23)) → (z 1 7)) →
    -- core premise 27; source assertion 780
    (((z 1 24)) → (z 1 8)) →
    -- core premise 28; source assertion 791
    (((z 1 25)) → (z 1 9)) →
    -- core premise 29; source assertion 798
    (((z 1 26)) → (z 1 10)) →
    -- core premise 30; source assertion 803
    (((z 1 27)) → (z 1 11)) →
    -- core premise 31; source assertion 808
    (((z 1 28)) → (z 1 12)) →
    -- core premise 32; source assertion 813
    (((z 1 29)) → (z 1 13)) →
    -- core premise 33; source assertion 816
    (((z 1 30)) → (z 1 14)) →
    -- core premise 34; source assertion 818
    (((z 1 31)) → (z 1 15)) →
    -- core premise 35; source assertion 888
    (((a 0 3) > 0) → (z 1 3)) →
    -- core premise 36; source assertion 892
    (((a 0 5) > 0) → (z 1 5)) →
    -- core premise 37; source assertion 894
    (((a 0 6) > 0) → (z 1 6)) →
    -- core premise 38; source assertion 896
    (((a 0 7) > 0) → (z 1 7)) →
    -- core premise 39; source assertion 900
    (((a 0 9) > 0) → (z 1 9)) →
    -- core premise 40; source assertion 902
    (((a 0 10) > 0) → (z 1 10)) →
    -- core premise 41; source assertion 904
    (((a 0 11) > 0) → (z 1 11)) →
    -- core premise 42; source assertion 906
    (((a 0 12) > 0) → (z 1 12)) →
    -- core premise 43; source assertion 908
    (((a 0 13) > 0) → (z 1 13)) →
    -- core premise 44; source assertion 910
    (((a 0 14) > 0) → (z 1 14)) →
    -- core premise 45; source assertion 912
    (((a 0 15) > 0) → (z 1 15)) →
    -- core premise 46; source assertion 916
    (((a 0 17) > 0) → (z 1 17)) →
    -- core premise 47; source assertion 918
    (((a 0 18) > 0) → (z 1 18)) →
    -- core premise 48; source assertion 920
    (((a 0 19) > 0) → (z 1 19)) →
    -- core premise 49; source assertion 922
    (((a 0 20) > 0) → (z 1 20)) →
    -- core premise 50; source assertion 924
    (((a 0 21) > 0) → (z 1 21)) →
    -- core premise 51; source assertion 926
    (((a 0 22) > 0) → (z 1 22)) →
    -- core premise 52; source assertion 928
    (((a 0 23) > 0) → (z 1 23)) →
    -- core premise 53; source assertion 930
    (((a 0 24) > 0) → (z 1 24)) →
    -- core premise 54; source assertion 932
    (((a 0 25) > 0) → (z 1 25)) →
    -- core premise 55; source assertion 934
    (((a 0 26) > 0) → (z 1 26)) →
    -- core premise 56; source assertion 936
    (((a 0 27) > 0) → (z 1 27)) →
    -- core premise 57; source assertion 938
    (((a 0 28) > 0) → (z 1 28)) →
    -- core premise 58; source assertion 940
    (((a 0 29) > 0) → (z 1 29)) →
    -- core premise 59; source assertion 942
    (((a 0 30) > 0) → (z 1 30)) →
    -- core premise 60; source assertion 944
    (((a 0 31) > 0) → (z 1 31)) →
    -- core premise 61; source assertion 946
    (((a 0 1) + (a 0 2) + (a 0 3) + (a 0 4) + (a 0 5) + (a 0 6) + (a 0 7) + (a 0 8) + (a 0 9) + (a 0 10) + (a 0 11) + (a 0 12) + (a 0 13) + (a 0 14) + (a 0 15) + (a 0 16) + (a 0 17) + (a 0 18) + (a 0 19) + (a 0 20) + (a 0 21) + (a 0 22) + (a 0 23) + (a 0 24) + (a 0 25) + (a 0 26) + (a 0 27) + (a 0 28) + (a 0 29) + (a 0 30) + (a 0 31)) > 0) →
    False

theorem collisionUnsatAt_1_of_k1CollisionCompactShardedRawCertificate
    (hraw : K1CollisionCompactShardedRawCertificate) : CollisionUnsatAt 1 (axisSupportOfMask 0) := by
  intro a z hconstraints hcollision
  unfold K1CollisionCompactShardedRawCertificate at hraw
  apply hraw
    (fun s m => a s (axisSupportOfMask m.val))
    (fun s m => z s (axisSupportOfMask m.val))
  · exact k1CollisionCompactShardedCorePremise0 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise1 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise2 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise3 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise4 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise5 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise6 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise7 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise8 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise9 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise10 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise11 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise12 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise13 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise14 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise15 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise16 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise17 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise18 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise19 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise20 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise21 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise22 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise23 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise24 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise25 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise26 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise27 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise28 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise29 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise30 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise31 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise32 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise33 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise34 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise35 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise36 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise37 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise38 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise39 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise40 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise41 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise42 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise43 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise44 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise45 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise46 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise47 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise48 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise49 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise50 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise51 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise52 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise53 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise54 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise55 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise56 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise57 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise58 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise59 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise60 a z hconstraints
  · exact k1CollisionCompactShardedCorePremise61 a z hconstraints hcollision

end Fuglede
