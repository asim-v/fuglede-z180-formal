import Fuglede.CampaignBatch00.NormalizedTypedPremiseBatch00
import Fuglede.CampaignBatch00.NormalizedTypedPremiseBatch01

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Compact typed adapter for pinned collision k=2.
SMT SHA-256: `97f31d7a9a4f118c56bd00f9788e1800d9bd96a906d412b777d1eae2ac28910e`.
Core-index SHA-256: `af075d3fac182a018e898142cf7cb38ef39031281deaee13d7a29290e3912897`.
Normalized-premise route: `true`.
-/

namespace Fuglede

def K2CollisionNormalizedRawCertificate : Prop :=
  ∀ (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop),
    -- core premise 0; source assertion 222
    ((a 0 2) = 0) →
    -- core premise 1; source assertion 224
    ((a 0 4) = 0) →
    -- core premise 2; source assertion 226
    ((a 0 8) = 0) →
    -- core premise 3; source assertion 228
    ((a 0 16) = 0) →
    -- core premise 4; source assertion 645
    (¬ (z 1 2)) →
    -- core premise 5; source assertion 647
    (¬ (z 1 4)) →
    -- core premise 6; source assertion 649
    (¬ (z 1 8)) →
    -- core premise 7; source assertion 698
    (((z 1 6)) → (z 1 2)) →
    -- core premise 8; source assertion 700
    (((z 1 10)) → (z 1 2)) →
    -- core premise 9; source assertion 704
    (((z 1 18)) → (z 1 2)) →
    -- core premise 10; source assertion 721
    (((z 1 12)) → (z 1 4)) →
    -- core premise 11; source assertion 725
    (((z 1 20)) → (z 1 4)) →
    -- core premise 12; source assertion 740
    (((z 1 14)) → (z 1 6)) →
    -- core premise 13; source assertion 742
    (((z 1 22)) → (z 1 6)) →
    -- core premise 14; source assertion 755
    (((z 1 24)) → (z 1 8)) →
    -- core premise 15; source assertion 772
    (((z 1 26)) → (z 1 10)) →
    -- core premise 16; source assertion 781
    (((z 1 28)) → (z 1 12)) →
    -- core premise 17; source assertion 788
    (((z 1 30)) → (z 1 14)) →
    -- core premise 18; source assertion 858
    (((a 0 6) > 0) → (z 1 6)) →
    -- core premise 19; source assertion 866
    (((a 0 10) > 0) → (z 1 10)) →
    -- core premise 20; source assertion 870
    (((a 0 12) > 0) → (z 1 12)) →
    -- core premise 21; source assertion 874
    (((a 0 14) > 0) → (z 1 14)) →
    -- core premise 22; source assertion 882
    (((a 0 18) > 0) → (z 1 18)) →
    -- core premise 23; source assertion 886
    (((a 0 20) > 0) → (z 1 20)) →
    -- core premise 24; source assertion 890
    (((a 0 22) > 0) → (z 1 22)) →
    -- core premise 25; source assertion 894
    (((a 0 24) > 0) → (z 1 24)) →
    -- core premise 26; source assertion 898
    (((a 0 26) > 0) → (z 1 26)) →
    -- core premise 27; source assertion 902
    (((a 0 28) > 0) → (z 1 28)) →
    -- core premise 28; source assertion 906
    (((a 0 30) > 0) → (z 1 30)) →
    -- core premise 29; source assertion 910
    (((a 0 2) + (a 0 4) + (a 0 6) + (a 0 8) + (a 0 10) + (a 0 12) + (a 0 14) + (a 0 16) + (a 0 18) + (a 0 20) + (a 0 22) + (a 0 24) + (a 0 26) + (a 0 28) + (a 0 30)) > 0) →
    False

theorem collisionUnsatAt_2_of_k2CollisionNormalizedRawCertificate
    (hraw : K2CollisionNormalizedRawCertificate) : CollisionUnsatAt 2 (axisSupportOfMask 1) := by
  intro a z hconstraints hcollision
  unfold K2CollisionNormalizedRawCertificate at hraw
  apply hraw
    (fun s m => a s (axisSupportOfMask m.val))
    (fun s m => z s (axisSupportOfMask m.val))
  · exact k2CollisionNormalizedCorePremise0 a z hconstraints
  · exact k2CollisionNormalizedCorePremise1 a z hconstraints
  · exact k2CollisionNormalizedCorePremise2 a z hconstraints
  · exact k2CollisionNormalizedCorePremise3 a z hconstraints
  · exact k2CollisionNormalizedCorePremise4 a z hconstraints
  · exact k2CollisionNormalizedCorePremise5 a z hconstraints
  · exact k2CollisionNormalizedCorePremise6 a z hconstraints
  · exact k2CollisionNormalizedCorePremise7 a z hconstraints
  · exact k2CollisionNormalizedCorePremise8 a z hconstraints
  · exact k2CollisionNormalizedCorePremise9 a z hconstraints
  · exact k2CollisionNormalizedCorePremise10 a z hconstraints
  · exact k2CollisionNormalizedCorePremise11 a z hconstraints
  · exact k2CollisionNormalizedCorePremise12 a z hconstraints
  · exact k2CollisionNormalizedCorePremise13 a z hconstraints
  · exact k2CollisionNormalizedCorePremise14 a z hconstraints
  · exact k2CollisionNormalizedCorePremise15 a z hconstraints
  · exact k2CollisionNormalizedCorePremise16 a z hconstraints
  · exact k2CollisionNormalizedCorePremise17 a z hconstraints
  · exact k2CollisionNormalizedCorePremise18 a z hconstraints
  · exact k2CollisionNormalizedCorePremise19 a z hconstraints
  · exact k2CollisionNormalizedCorePremise20 a z hconstraints
  · exact k2CollisionNormalizedCorePremise21 a z hconstraints
  · exact k2CollisionNormalizedCorePremise22 a z hconstraints
  · exact k2CollisionNormalizedCorePremise23 a z hconstraints
  · exact k2CollisionNormalizedCorePremise24 a z hconstraints
  · exact k2CollisionNormalizedCorePremise25 a z hconstraints
  · exact k2CollisionNormalizedCorePremise26 a z hconstraints
  · exact k2CollisionNormalizedCorePremise27 a z hconstraints
  · exact k2CollisionNormalizedCorePremise28 a z hconstraints
  · exact k2CollisionNormalizedCorePremise29 a z hconstraints hcollision

end Fuglede
