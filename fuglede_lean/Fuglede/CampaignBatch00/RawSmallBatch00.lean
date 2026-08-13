import Mathlib.Tactic

/-! Experimental raw-proof batch.  Provenance is per theorem block. -/

-- BEGIN collision-k2-side0
-- Full SMT source: fuglede_search/multiaxis_low_1_22_proofs/k2_collision_side0.smt2
-- Full SMT SHA-256: 97f31d7a9a4f118c56bd00f9788e1800d9bd96a906d412b777d1eae2ac28910e
-- Selected core-index: fuglede_search/qflra_representative_scan/cores/k2-collision-indices.json
-- Selected core-index SHA-256: af075d3fac182a018e898142cf7cb38ef39031281deaee13d7a29290e3912897
-- Tree evidence: fuglede_search/qflra_representative_scan/cases/k2-collision.json
-- Tree evidence SHA-256: 1263aba36e419a0549c674aa73c3c98e34af7d34ae874f4d2872cc8a95d69208
-- SMT declarations: 126; compact Lean families: 2; selected assertions: 30

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! This file is generated fail-closed from the named SMT-LIB instance. -/

theorem fuglede_k2_collision_static_core_compact
    (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop)
    (h0 : ((a 0 2) = 0))
    (h1 : ((a 0 4) = 0))
    (h2 : ((a 0 8) = 0))
    (h3 : ((a 0 16) = 0))
    (h4 : (¬ (z 1 2)))
    (h5 : (¬ (z 1 4)))
    (h6 : (¬ (z 1 8)))
    (h7 : (((z 1 6)) → (z 1 2)))
    (h8 : (((z 1 10)) → (z 1 2)))
    (h9 : (((z 1 18)) → (z 1 2)))
    (h10 : (((z 1 12)) → (z 1 4)))
    (h11 : (((z 1 20)) → (z 1 4)))
    (h12 : (((z 1 14)) → (z 1 6)))
    (h13 : (((z 1 22)) → (z 1 6)))
    (h14 : (((z 1 24)) → (z 1 8)))
    (h15 : (((z 1 26)) → (z 1 10)))
    (h16 : (((z 1 28)) → (z 1 12)))
    (h17 : (((z 1 30)) → (z 1 14)))
    (h18 : (((a 0 6) > 0) → (z 1 6)))
    (h19 : (((a 0 10) > 0) → (z 1 10)))
    (h20 : (((a 0 12) > 0) → (z 1 12)))
    (h21 : (((a 0 14) > 0) → (z 1 14)))
    (h22 : (((a 0 18) > 0) → (z 1 18)))
    (h23 : (((a 0 20) > 0) → (z 1 20)))
    (h24 : (((a 0 22) > 0) → (z 1 22)))
    (h25 : (((a 0 24) > 0) → (z 1 24)))
    (h26 : (((a 0 26) > 0) → (z 1 26)))
    (h27 : (((a 0 28) > 0) → (z 1 28)))
    (h28 : (((a 0 30) > 0) → (z 1 30)))
    (h29 : (((a 0 2) + (a 0 4) + (a 0 6) + (a 0 8) + (a 0 10) + (a 0 12) + (a 0 14) + (a 0 16) + (a 0 18) + (a 0 20) + (a 0 22) + (a 0 24) + (a 0 26) + (a 0 28) + (a 0 30)) > 0))
    : False := by
  by_cases d0 : ((a 0 6) > 0)
  · simp_all
  · have d0_not : ((a 0 6) ≤ 0) := not_lt.mp d0
    by_cases d1 : ((a 0 10) > 0)
    · simp_all
    · have d1_not : ((a 0 10) ≤ 0) := not_lt.mp d1
      by_cases d2 : ((a 0 12) > 0)
      · simp_all
      · have d2_not : ((a 0 12) ≤ 0) := not_lt.mp d2
        by_cases d3 : ((a 0 14) > 0)
        · simp_all
        · have d3_not : ((a 0 14) ≤ 0) := not_lt.mp d3
          by_cases d4 : ((a 0 18) > 0)
          · simp_all
          · have d4_not : ((a 0 18) ≤ 0) := not_lt.mp d4
            by_cases d5 : ((a 0 20) > 0)
            · simp_all
            · have d5_not : ((a 0 20) ≤ 0) := not_lt.mp d5
              by_cases d6 : ((a 0 22) > 0)
              · simp_all
              · have d6_not : ((a 0 22) ≤ 0) := not_lt.mp d6
                by_cases d7 : ((a 0 24) > 0)
                · simp_all
                · have d7_not : ((a 0 24) ≤ 0) := not_lt.mp d7
                  by_cases d8 : ((a 0 26) > 0)
                  · simp_all
                  · have d8_not : ((a 0 26) ≤ 0) := not_lt.mp d8
                    by_cases d9 : ((a 0 28) > 0)
                    · simp_all
                    · have d9_not : ((a 0 28) ≤ 0) := not_lt.mp d9
                      by_cases d10 : ((a 0 30) > 0)
                      · simp_all
                      · have d10_not : ((a 0 30) ≤ 0) := not_lt.mp d10
                        linarith only [h0, h1, h2, h3, h29, d0_not, d1_not, d2_not, d3_not, d4_not, d5_not, d6_not, d7_not, d8_not, d9_not, d10_not]

#print axioms fuglede_k2_collision_static_core_compact

-- END collision-k2-side0

-- BEGIN base-k4
-- Full SMT source: fuglede_search/multiaxis_low_1_22_proofs/k4.smt2
-- Full SMT SHA-256: 8047d44ede7ada27cde8eda3f81e9ee528a8d3a6b163088c537b915206df4978
-- Selected core-index: fuglede_search/campaign_compact_batch_experiment/prototype_v2/evidence/k4/K4BaseCompact_core31_indices.json
-- Selected core-index SHA-256: 0d0e5142e7826cc5bd7f8ea35b6a4759fa0bc15ee5610668314b670537568502
-- Tree evidence: fuglede_search/campaign_compact_batch_experiment/prototype_v2/evidence/k4/K4BaseCompact_core31_tree.json
-- Tree evidence SHA-256: 1943de9eaef504bf130b72c6a1da1c0b79a1047afe8434678e8e49654dcb855b
-- SMT declarations: 126; compact Lean families: 2; assertions: 31

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! This file is generated fail-closed from the named SMT-LIB instance. -/

theorem fuglede_k4_base_core_compact
    (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop)
    (h0 : ((a 0 0) = 4))
    (h1 : (((a 0 0) + (a 0 2) + (a 0 4) + (a 0 6) + (a 0 8) + (a 0 10) + (a 0 12) + (a 0 14) + (a 0 16) + (a 0 18) + (a 0 20) + (a 0 22) + (a 0 24) + (a 0 26) + (a 0 28) + (a 0 30)) ≥ 8))
    (h2 : ((a 0 2) = 0))
    (h3 : ((a 0 4) = 0))
    (h4 : ((a 0 8) = 0))
    (h5 : ((a 0 16) = 0))
    (h6 : (¬ (z 1 2)))
    (h7 : (¬ (z 1 4)))
    (h8 : (¬ (z 1 8)))
    (h9 : (((z 1 6)) → (z 1 2)))
    (h10 : (((z 1 10)) → (z 1 2)))
    (h11 : (((z 1 18)) → (z 1 2)))
    (h12 : (((z 1 12)) → (z 1 4)))
    (h13 : (((z 1 20)) → (z 1 4)))
    (h14 : (((z 1 14)) → (z 1 6)))
    (h15 : (((z 1 22)) → (z 1 6)))
    (h16 : (((z 1 24)) → (z 1 8)))
    (h17 : (((z 1 26)) → (z 1 10)))
    (h18 : (((z 1 28)) → (z 1 12)))
    (h19 : (((z 1 30)) → (z 1 14)))
    (h20 : (((a 0 6) > 0) → (z 1 6)))
    (h21 : (((a 0 10) > 0) → (z 1 10)))
    (h22 : (((a 0 12) > 0) → (z 1 12)))
    (h23 : (((a 0 14) > 0) → (z 1 14)))
    (h24 : (((a 0 18) > 0) → (z 1 18)))
    (h25 : (((a 0 20) > 0) → (z 1 20)))
    (h26 : (((a 0 22) > 0) → (z 1 22)))
    (h27 : (((a 0 24) > 0) → (z 1 24)))
    (h28 : (((a 0 26) > 0) → (z 1 26)))
    (h29 : (((a 0 28) > 0) → (z 1 28)))
    (h30 : (((a 0 30) > 0) → (z 1 30)))
    : False := by
  by_cases d0 : ((a 0 6) > 0)
  · simp_all
  · have d0_not : ((a 0 6) ≤ 0) := not_lt.mp d0
    by_cases d1 : ((a 0 10) > 0)
    · simp_all
    · have d1_not : ((a 0 10) ≤ 0) := not_lt.mp d1
      by_cases d2 : ((a 0 12) > 0)
      · simp_all
      · have d2_not : ((a 0 12) ≤ 0) := not_lt.mp d2
        by_cases d3 : ((a 0 14) > 0)
        · simp_all
        · have d3_not : ((a 0 14) ≤ 0) := not_lt.mp d3
          by_cases d4 : ((a 0 18) > 0)
          · simp_all
          · have d4_not : ((a 0 18) ≤ 0) := not_lt.mp d4
            by_cases d5 : ((a 0 20) > 0)
            · simp_all
            · have d5_not : ((a 0 20) ≤ 0) := not_lt.mp d5
              by_cases d6 : ((a 0 22) > 0)
              · simp_all
              · have d6_not : ((a 0 22) ≤ 0) := not_lt.mp d6
                by_cases d7 : ((a 0 24) > 0)
                · simp_all
                · have d7_not : ((a 0 24) ≤ 0) := not_lt.mp d7
                  by_cases d8 : ((a 0 26) > 0)
                  · simp_all
                  · have d8_not : ((a 0 26) ≤ 0) := not_lt.mp d8
                    by_cases d9 : ((a 0 28) > 0)
                    · simp_all
                    · have d9_not : ((a 0 28) ≤ 0) := not_lt.mp d9
                      by_cases d10 : ((a 0 30) > 0)
                      · simp_all
                      · have d10_not : ((a 0 30) ≤ 0) := not_lt.mp d10
                        linarith only [h0, h1, h2, h3, h4, h5, d0_not, d1_not, d2_not, d3_not, d4_not, d5_not, d6_not, d7_not, d8_not, d9_not, d10_not]

#print axioms fuglede_k4_base_core_compact

-- END base-k4
