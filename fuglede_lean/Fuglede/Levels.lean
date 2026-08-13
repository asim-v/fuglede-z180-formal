import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

/-!
# Levels of a finite subset of a product

The arguments for square-free cyclic groups repeatedly write a finite set in
`G × H` as a collection of `H`-levels.  This file records the elementary
counting facts behind that decomposition.  They are deliberately stated for
arbitrary finite types, so the later CRT layer can use them without importing
any cyclic-group arithmetic.
-/

namespace Fuglede

section Levels

variable {α β : Type*} [DecidableEq β]

/-- The `b`-level of `A ⊆ α × β`, retained as a finset of pairs. -/
def level (A : Finset (α × β)) (b : β) : Finset (α × β) :=
  A.filter fun x => x.2 = b

@[simp]
theorem mem_level {A : Finset (α × β)} {b : β} {x : α × β} :
    x ∈ level A b ↔ x ∈ A ∧ x.2 = b := by
  simp [level]

/-- Different levels are disjoint. -/
theorem disjoint_level {A : Finset (α × β)} {b c : β} (hbc : b ≠ c) :
    Disjoint (level A b) (level A c) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxb hxc
  exact hbc ((mem_level.mp hxb).2.symm.trans (mem_level.mp hxc).2)

/-- Over all values of the second coordinate, the levels recover `A`. -/
theorem biUnion_level_eq [DecidableEq α] [Fintype β] (A : Finset (α × β)) :
    Finset.univ.biUnion (level A) = A := by
  classical
  ext x
  simp [level]

/-- The cardinalities of all levels add up to the cardinality of the set. -/
theorem sum_card_level [Fintype β] (A : Finset (α × β)) :
    (∑ b : β, (level A b).card) = A.card := by
  classical
  simpa [level] using
    (Finset.sum_card_fiberwise_eq_card_filter A (Finset.univ : Finset β) Prod.snd)

/-- If every level has cardinality `k`, then the whole set has cardinality
`|β| * k`.  This is the elementary count used after a levelwise argument
forces equicardinality of the fibers. -/
theorem card_eq_card_mul_of_card_level_eq [Fintype β]
    (A : Finset (α × β)) (k : ℕ) (h : ∀ b : β, (level A b).card = k) :
    A.card = Fintype.card β * k := by
  rw [← sum_card_level A]
  simp [h]

/-- In particular, balanced levels force the number of levels to divide the
total cardinality. -/
theorem card_fintype_dvd_card_of_card_level_eq [Fintype β]
    (A : Finset (α × β)) (k : ℕ) (h : ∀ b : β, (level A b).card = k) :
    Fintype.card β ∣ A.card := by
  exact ⟨k, card_eq_card_mul_of_card_level_eq A k h⟩

end Levels

end Fuglede
