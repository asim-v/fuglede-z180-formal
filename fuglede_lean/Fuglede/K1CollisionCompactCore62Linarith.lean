-- Full SMT source: fuglede_search/multiaxis_low_1_22_proofs/k1_collision_side0.smt2
-- Full SMT SHA-256: 89b3e0fa4644c71bcca195f1964ffb4dddcf4910b0debda71dfa93237b4b8699
-- Selected core-index SHA-256: ddda8c7134e39af7bcffc0f381cfd2c774df6f03d06ce5bab77c74b250b5a648
-- SMT declarations: 126; compact Lean families: 2; selected assertions: 62
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! This file is generated fail-closed from the named SMT-LIB instance. -/

theorem fuglede_k1_collision_side0_compact
    (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop)
    (h0 : ((a 0 1) = 0))
    (h1 : ((a 0 2) = 0))
    (h2 : ((a 0 4) = 0))
    (h3 : ((a 0 8) = 0))
    (h4 : ((a 0 16) = 0))
    (h5 : (¬ (z 1 1)))
    (h6 : (¬ (z 1 2)))
    (h7 : (¬ (z 1 4)))
    (h8 : (¬ (z 1 8)))
    (h9 : (((z 1 3)) → (z 1 1)))
    (h10 : (((z 1 5)) → (z 1 1)))
    (h11 : (((z 1 9)) → (z 1 1)))
    (h12 : (((z 1 17)) → (z 1 1)))
    (h13 : (((z 1 6)) → (z 1 2)))
    (h14 : (((z 1 10)) → (z 1 2)))
    (h15 : (((z 1 18)) → (z 1 2)))
    (h16 : (((z 1 7)) → (z 1 3)))
    (h17 : (((z 1 11)) → (z 1 3)))
    (h18 : (((z 1 19)) → (z 1 3)))
    (h19 : (((z 1 12)) → (z 1 4)))
    (h20 : (((z 1 20)) → (z 1 4)))
    (h21 : (((z 1 13)) → (z 1 5)))
    (h22 : (((z 1 21)) → (z 1 5)))
    (h23 : (((z 1 14)) → (z 1 6)))
    (h24 : (((z 1 22)) → (z 1 6)))
    (h25 : (((z 1 15)) → (z 1 7)))
    (h26 : (((z 1 23)) → (z 1 7)))
    (h27 : (((z 1 24)) → (z 1 8)))
    (h28 : (((z 1 25)) → (z 1 9)))
    (h29 : (((z 1 26)) → (z 1 10)))
    (h30 : (((z 1 27)) → (z 1 11)))
    (h31 : (((z 1 28)) → (z 1 12)))
    (h32 : (((z 1 29)) → (z 1 13)))
    (h33 : (((z 1 30)) → (z 1 14)))
    (h34 : (((z 1 31)) → (z 1 15)))
    (h35 : (((a 0 3) > 0) → (z 1 3)))
    (h36 : (((a 0 5) > 0) → (z 1 5)))
    (h37 : (((a 0 6) > 0) → (z 1 6)))
    (h38 : (((a 0 7) > 0) → (z 1 7)))
    (h39 : (((a 0 9) > 0) → (z 1 9)))
    (h40 : (((a 0 10) > 0) → (z 1 10)))
    (h41 : (((a 0 11) > 0) → (z 1 11)))
    (h42 : (((a 0 12) > 0) → (z 1 12)))
    (h43 : (((a 0 13) > 0) → (z 1 13)))
    (h44 : (((a 0 14) > 0) → (z 1 14)))
    (h45 : (((a 0 15) > 0) → (z 1 15)))
    (h46 : (((a 0 17) > 0) → (z 1 17)))
    (h47 : (((a 0 18) > 0) → (z 1 18)))
    (h48 : (((a 0 19) > 0) → (z 1 19)))
    (h49 : (((a 0 20) > 0) → (z 1 20)))
    (h50 : (((a 0 21) > 0) → (z 1 21)))
    (h51 : (((a 0 22) > 0) → (z 1 22)))
    (h52 : (((a 0 23) > 0) → (z 1 23)))
    (h53 : (((a 0 24) > 0) → (z 1 24)))
    (h54 : (((a 0 25) > 0) → (z 1 25)))
    (h55 : (((a 0 26) > 0) → (z 1 26)))
    (h56 : (((a 0 27) > 0) → (z 1 27)))
    (h57 : (((a 0 28) > 0) → (z 1 28)))
    (h58 : (((a 0 29) > 0) → (z 1 29)))
    (h59 : (((a 0 30) > 0) → (z 1 30)))
    (h60 : (((a 0 31) > 0) → (z 1 31)))
    (h61 : (((a 0 1) + (a 0 2) + (a 0 3) + (a 0 4) + (a 0 5) + (a 0 6) + (a 0 7) + (a 0 8) + (a 0 9) + (a 0 10) + (a 0 11) + (a 0 12) + (a 0 13) + (a 0 14) + (a 0 15) + (a 0 16) + (a 0 17) + (a 0 18) + (a 0 19) + (a 0 20) + (a 0 21) + (a 0 22) + (a 0 23) + (a 0 24) + (a 0 25) + (a 0 26) + (a 0 27) + (a 0 28) + (a 0 29) + (a 0 30) + (a 0 31)) > 0))
    : False := by
  by_cases d0 : ((a 0 3) > 0)
  · simp_all
  · have d0_not : ((a 0 3) ≤ 0) := not_lt.mp d0
    by_cases d1 : ((a 0 5) > 0)
    · simp_all
    · have d1_not : ((a 0 5) ≤ 0) := not_lt.mp d1
      by_cases d2 : ((a 0 6) > 0)
      · simp_all
      · have d2_not : ((a 0 6) ≤ 0) := not_lt.mp d2
        by_cases d3 : ((a 0 7) > 0)
        · simp_all
        · have d3_not : ((a 0 7) ≤ 0) := not_lt.mp d3
          by_cases d4 : ((a 0 9) > 0)
          · simp_all
          · have d4_not : ((a 0 9) ≤ 0) := not_lt.mp d4
            by_cases d5 : ((a 0 10) > 0)
            · simp_all
            · have d5_not : ((a 0 10) ≤ 0) := not_lt.mp d5
              by_cases d6 : ((a 0 11) > 0)
              · simp_all
              · have d6_not : ((a 0 11) ≤ 0) := not_lt.mp d6
                by_cases d7 : ((a 0 12) > 0)
                · simp_all
                · have d7_not : ((a 0 12) ≤ 0) := not_lt.mp d7
                  by_cases d8 : ((a 0 13) > 0)
                  · simp_all
                  · have d8_not : ((a 0 13) ≤ 0) := not_lt.mp d8
                    by_cases d9 : ((a 0 14) > 0)
                    · simp_all
                    · have d9_not : ((a 0 14) ≤ 0) := not_lt.mp d9
                      by_cases d10 : ((a 0 15) > 0)
                      · simp_all
                      · have d10_not : ((a 0 15) ≤ 0) := not_lt.mp d10
                        by_cases d11 : ((a 0 17) > 0)
                        · simp_all
                        · have d11_not : ((a 0 17) ≤ 0) := not_lt.mp d11
                          by_cases d12 : ((a 0 18) > 0)
                          · simp_all
                          · have d12_not : ((a 0 18) ≤ 0) := not_lt.mp d12
                            by_cases d13 : ((a 0 19) > 0)
                            · simp_all
                            · have d13_not : ((a 0 19) ≤ 0) := not_lt.mp d13
                              by_cases d14 : ((a 0 20) > 0)
                              · simp_all
                              · have d14_not : ((a 0 20) ≤ 0) := not_lt.mp d14
                                by_cases d15 : ((a 0 21) > 0)
                                · simp_all
                                · have d15_not : ((a 0 21) ≤ 0) := not_lt.mp d15
                                  by_cases d16 : ((a 0 22) > 0)
                                  · simp_all
                                  · have d16_not : ((a 0 22) ≤ 0) := not_lt.mp d16
                                    by_cases d17 : ((a 0 23) > 0)
                                    · simp_all
                                    · have d17_not : ((a 0 23) ≤ 0) := not_lt.mp d17
                                      by_cases d18 : ((a 0 24) > 0)
                                      · simp_all
                                      · have d18_not : ((a 0 24) ≤ 0) := not_lt.mp d18
                                        by_cases d19 : ((a 0 25) > 0)
                                        · simp_all
                                        · have d19_not : ((a 0 25) ≤ 0) := not_lt.mp d19
                                          by_cases d20 : ((a 0 26) > 0)
                                          · simp_all
                                          · have d20_not : ((a 0 26) ≤ 0) := not_lt.mp d20
                                            by_cases d21 : ((a 0 27) > 0)
                                            · simp_all
                                            · have d21_not : ((a 0 27) ≤ 0) := not_lt.mp d21
                                              by_cases d22 : ((a 0 28) > 0)
                                              · simp_all
                                              · have d22_not : ((a 0 28) ≤ 0) := not_lt.mp d22
                                                by_cases d23 : ((a 0 29) > 0)
                                                · simp_all
                                                · have d23_not : ((a 0 29) ≤ 0) := not_lt.mp d23
                                                  by_cases d24 : ((a 0 30) > 0)
                                                  · simp_all
                                                  · have d24_not : ((a 0 30) ≤ 0) := not_lt.mp d24
                                                    by_cases d25 : ((a 0 31) > 0)
                                                    · simp_all
                                                    · have d25_not : ((a 0 31) ≤ 0) := not_lt.mp d25
                                                      linarith only [h0, h1, h2, h3, h4, h61, d0_not, d1_not, d2_not, d3_not, d4_not, d5_not, d6_not, d7_not, d8_not, d9_not, d10_not, d11_not, d12_not, d13_not, d14_not, d15_not, d16_not, d17_not, d18_not, d19_not, d20_not, d21_not, d22_not, d23_not, d24_not, d25_not]

#print axioms fuglede_k1_collision_side0_compact
