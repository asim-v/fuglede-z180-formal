-- Full SMT source: fuglede_search/multiaxis_k77_branches/k77_collision_side0_mask01_order2.smt2
-- Full SMT SHA-256: 9aa103c66ca1a2303e589a768d28fa13d2a789be95f0d1c56a59b1a1c615d3c7
-- Selected core-index SHA-256: a95ff7bd531dda3be77b2b515af5d15bdc1fda99d3451f40aa2db5681b8ec356
-- SMT declarations: 126; compact Lean families: 2; selected assertions: 2
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! This file is generated fail-closed from the named SMT-LIB instance. -/

theorem fuglede_k77_branch_side0_mask01_compact
    (a : Fin 2 → Fin 32 → Int)
    (z : Fin 2 → Fin 32 → Prop)
    (h0 : ((a 0 1) = 0))
    (h1 : ((a 0 1) > 0))
    : False := by
  linarith only [h0, h1]

#print axioms fuglede_k77_branch_side0_mask01_compact
