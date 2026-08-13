import Fuglede.ExactOrderDistribution
import Mathlib.Tactic

/-!
# Finite difference-order classifier: core definitions

The exhaustive part is split into small kernel-reduced shards.  Each shard
checks four-element remainders after two translated points (`0` and `a`) have
been fixed.  Thus `decide` ranges over `C(34,4)`, never over all finsets.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def Z36HasDifferenceOrder (L : Finset (ZMod 36)) (m : Nat) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧ frequencyOrder 36 (x - y) = m

instance (L : Finset (ZMod 36)) (m : Nat) :
    Decidable (Z36HasDifferenceOrder L m) := by
  unfold Z36HasDifferenceOrder
  infer_instance

/-- The exact nine-element antichain of minimal difference-order patterns
for a six-element subset of `ZMod 36`. -/
def Z36Card6NineDifferencePatterns (L : Finset (ZMod 36)) : Prop :=
  (Z36HasDifferenceOrder L 2 ∧ Z36HasDifferenceOrder L 3 ∧
      Z36HasDifferenceOrder L 6) ∨
  (Z36HasDifferenceOrder L 2 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 18) ∨
  (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 4 ∧
      Z36HasDifferenceOrder L 12) ∨
  (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 9) ∨
  (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 18) ∨
  (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 36) ∨
  (Z36HasDifferenceOrder L 4 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 36) ∨
  (Z36HasDifferenceOrder L 6 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 18) ∨
  (Z36HasDifferenceOrder L 9 ∧ Z36HasDifferenceOrder L 12 ∧
      Z36HasDifferenceOrder L 36)

instance (L : Finset (ZMod 36)) :
    Decidable (Z36Card6NineDifferencePatterns L) := by
  unfold Z36Card6NineDifferencePatterns
  infer_instance

/-- Candidate four-point remainder after fixing translated points `0,a`. -/
def z36Card6RemainderCandidates (a : ZMod 36) :
    Finset (Finset (ZMod 36)) :=
  ((Finset.univ.erase 0).erase a).powersetCard 4

theorem z36_mem_remainderCandidates_iff
    {a : ZMod 36} {S : Finset (ZMod 36)} :
    S ∈ z36Card6RemainderCandidates a ↔
      S.card = 4 ∧ S ⊆ (Finset.univ.erase 0).erase a := by
  simp [z36Card6RemainderCandidates, and_comm]

end Fuglede
