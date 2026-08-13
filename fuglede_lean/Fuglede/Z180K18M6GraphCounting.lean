import Fuglede.Z180K18M6GraphFiberInterface

/-!
# Fibre-cardinality bookkeeping for the K18 `m = 6` graph

These lemmas contain no graph theory.  They turn the geometric assertion
that at most two fifth-coordinate fibres are double into the global bound
seven in the all-small-fibres case.
-/

namespace Fuglede

open scoped BigOperators

theorem z180_k18_m6_sum_fibre_cards (L : Finset (ZMod 180)) :
    (∑ c : ZMod 5, (z180K18M6Fibre L c).card) = L.card := by
  classical
  simpa [z180K18M6Fibre, z180K18M6Fifth] using
    (Finset.sum_card_fiberwise_eq_card_filter L
      (Finset.univ : Finset (ZMod 5))
      (fun x : ZMod 180 => (ZMod.cast x : ZMod 5)))

theorem z180_k18_m6_small_fibres_card_le_seven
    (L : Finset (ZMod 180))
    (hall : ∀ c : ZMod 5, (z180K18M6Fibre L c).card ≤ 2)
    (hdouble : Z180K18M6DoubleFibreBound L) :
    L.card ≤ 7 := by
  classical
  let n : ZMod 5 → Nat := fun c => (z180K18M6Fibre L c).card
  let D : Finset (ZMod 5) := z180K18M6DoubleFibres L
  have hpoint : ∀ c : ZMod 5, n c ≤ 1 + if c ∈ D then 1 else 0 := by
    intro c
    by_cases hc : 2 ≤ n c
    · have hcD : c ∈ D := by
        simp [D, z180K18M6DoubleFibres, n, hc]
      simp [hcD]
      exact hall c
    · have hcD : c ∉ D := by
        simp [D, z180K18M6DoubleFibres, n, hc]
      simp [hcD]
      omega
  have hsumle : (∑ c : ZMod 5, n c) ≤
      ∑ c : ZMod 5, (1 + if c ∈ D then 1 else 0) := by
    exact Finset.sum_le_sum fun c _ => hpoint c
  have hright : (∑ c : ZMod 5, (1 + if c ∈ D then 1 else 0)) =
      5 + D.card := by
    simp [Finset.sum_add_distrib, Finset.sum_boole]
  have hD : D.card ≤ 2 := by
    simpa [D, Z180K18M6DoubleFibreBound] using hdouble
  have hsum := z180_k18_m6_sum_fibre_cards L
  change (∑ c : ZMod 5, n c) = L.card at hsum
  omega

#print axioms z180_k18_m6_sum_fibre_cards
#print axioms z180_k18_m6_small_fibres_card_le_seven

end Fuglede
