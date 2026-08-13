import Fuglede.CampaignBatch00.NormalizedTypedPremiseBatch00
import Fuglede.CampaignBatch00.NormalizedTypedPremiseBatch01

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Compact typed adapter for pinned base k=4.
SMT SHA-256: `8047d44ede7ada27cde8eda3f81e9ee528a8d3a6b163088c537b915206df4978`.
Core-index SHA-256: `0d0e5142e7826cc5bd7f8ea35b6a4759fa0bc15ee5610668314b670537568502`.
Normalized-premise route: `true`.
-/

namespace Fuglede

def K4BaseNormalizedRawCertificate : Prop :=
  ∀ (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop),
    -- core premise 0; source assertion 0
    ((a 0 0) = 4) →
    -- core premise 1; source assertion 97
    (((a 0 0) + (a 0 2) + (a 0 4) + (a 0 6) + (a 0 8) + (a 0 10) + (a 0 12) + (a 0 14) + (a 0 16) + (a 0 18) + (a 0 20) + (a 0 22) + (a 0 24) + (a 0 26) + (a 0 28) + (a 0 30)) ≥ 8) →
    -- core premise 2; source assertion 222
    ((a 0 2) = 0) →
    -- core premise 3; source assertion 224
    ((a 0 4) = 0) →
    -- core premise 4; source assertion 226
    ((a 0 8) = 0) →
    -- core premise 5; source assertion 228
    ((a 0 16) = 0) →
    -- core premise 6; source assertion 629
    (¬ (z 1 2)) →
    -- core premise 7; source assertion 631
    (¬ (z 1 4)) →
    -- core premise 8; source assertion 633
    (¬ (z 1 8)) →
    -- core premise 9; source assertion 680
    (((z 1 6)) → (z 1 2)) →
    -- core premise 10; source assertion 682
    (((z 1 10)) → (z 1 2)) →
    -- core premise 11; source assertion 686
    (((z 1 18)) → (z 1 2)) →
    -- core premise 12; source assertion 702
    (((z 1 12)) → (z 1 4)) →
    -- core premise 13; source assertion 706
    (((z 1 20)) → (z 1 4)) →
    -- core premise 14; source assertion 720
    (((z 1 14)) → (z 1 6)) →
    -- core premise 15; source assertion 722
    (((z 1 22)) → (z 1 6)) →
    -- core premise 16; source assertion 734
    (((z 1 24)) → (z 1 8)) →
    -- core premise 17; source assertion 750
    (((z 1 26)) → (z 1 10)) →
    -- core premise 18; source assertion 758
    (((z 1 28)) → (z 1 12)) →
    -- core premise 19; source assertion 764
    (((z 1 30)) → (z 1 14)) →
    -- core premise 20; source assertion 826
    (((a 0 6) > 0) → (z 1 6)) →
    -- core premise 21; source assertion 834
    (((a 0 10) > 0) → (z 1 10)) →
    -- core premise 22; source assertion 838
    (((a 0 12) > 0) → (z 1 12)) →
    -- core premise 23; source assertion 842
    (((a 0 14) > 0) → (z 1 14)) →
    -- core premise 24; source assertion 850
    (((a 0 18) > 0) → (z 1 18)) →
    -- core premise 25; source assertion 854
    (((a 0 20) > 0) → (z 1 20)) →
    -- core premise 26; source assertion 858
    (((a 0 22) > 0) → (z 1 22)) →
    -- core premise 27; source assertion 862
    (((a 0 24) > 0) → (z 1 24)) →
    -- core premise 28; source assertion 866
    (((a 0 26) > 0) → (z 1 26)) →
    -- core premise 29; source assertion 870
    (((a 0 28) > 0) → (z 1 28)) →
    -- core premise 30; source assertion 874
    (((a 0 30) > 0) → (z 1 30)) →
    False

theorem baseUnsatAt_4_of_k4BaseNormalizedRawCertificate
    (hraw : K4BaseNormalizedRawCertificate) : BaseUnsatAt 4 := by
  intro a z hconstraints
  unfold K4BaseNormalizedRawCertificate at hraw
  apply hraw
    (fun s m => a s (axisSupportOfMask m.val))
    (fun s m => z s (axisSupportOfMask m.val))
  · exact k4BaseNormalizedCorePremise0 a z hconstraints
  · exact k4BaseNormalizedCorePremise1 a z hconstraints
  · exact k4BaseNormalizedCorePremise2 a z hconstraints
  · exact k4BaseNormalizedCorePremise3 a z hconstraints
  · exact k4BaseNormalizedCorePremise4 a z hconstraints
  · exact k4BaseNormalizedCorePremise5 a z hconstraints
  · exact k4BaseNormalizedCorePremise6 a z hconstraints
  · exact k4BaseNormalizedCorePremise7 a z hconstraints
  · exact k4BaseNormalizedCorePremise8 a z hconstraints
  · exact k4BaseNormalizedCorePremise9 a z hconstraints
  · exact k4BaseNormalizedCorePremise10 a z hconstraints
  · exact k4BaseNormalizedCorePremise11 a z hconstraints
  · exact k4BaseNormalizedCorePremise12 a z hconstraints
  · exact k4BaseNormalizedCorePremise13 a z hconstraints
  · exact k4BaseNormalizedCorePremise14 a z hconstraints
  · exact k4BaseNormalizedCorePremise15 a z hconstraints
  · exact k4BaseNormalizedCorePremise16 a z hconstraints
  · exact k4BaseNormalizedCorePremise17 a z hconstraints
  · exact k4BaseNormalizedCorePremise18 a z hconstraints
  · exact k4BaseNormalizedCorePremise19 a z hconstraints
  · exact k4BaseNormalizedCorePremise20 a z hconstraints
  · exact k4BaseNormalizedCorePremise21 a z hconstraints
  · exact k4BaseNormalizedCorePremise22 a z hconstraints
  · exact k4BaseNormalizedCorePremise23 a z hconstraints
  · exact k4BaseNormalizedCorePremise24 a z hconstraints
  · exact k4BaseNormalizedCorePremise25 a z hconstraints
  · exact k4BaseNormalizedCorePremise26 a z hconstraints
  · exact k4BaseNormalizedCorePremise27 a z hconstraints
  · exact k4BaseNormalizedCorePremise28 a z hconstraints
  · exact k4BaseNormalizedCorePremise29 a z hconstraints
  · exact k4BaseNormalizedCorePremise30 a z hconstraints

end Fuglede
