import Fuglede.Z36Card6DifferenceColorU1
import Fuglede.Z36Card6DifferenceColorU2
import Fuglede.Z36Card6DifferenceColorU3
import Fuglede.Z36Card6DifferenceColorU4
import Fuglede.Z36Card6DifferenceColorU5
import Fuglede.Z36Card6DifferenceColorU6
import Fuglede.Z36Card6DifferenceColorU7
import Fuglede.Z36Card6DifferenceColorU8
import Fuglede.Z36Card6DifferenceColorU9
import Mathlib.Tactic

/-!
# Structural difference-order classifier in `ZMod 36`

Negating the nine target patterns leaves nine maximal sets of allowed exact
difference orders.  Seven of their Cayley graphs have explicit proper
3- or 4-colorings.  For the remaining two, translating a clique to contain
zero and coloring the neighbors of zero gives a four-point bound.  The only
finite checks here are fixed `36 x 36` color-separation tables.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem z36_nonzero_order_cases {d : ZMod 36} (hd : d ≠ 0) :
    frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 3 ∨
    frequencyOrder 36 d = 4 ∨ frequencyOrder 36 d = 6 ∨
    frequencyOrder 36 d = 9 ∨ frequencyOrder 36 d = 12 ∨
    frequencyOrder 36 d = 18 ∨ frequencyOrder 36 d = 36 := by
  have hgt : 1 < frequencyOrder 36 d :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hd
  have hdvd : frequencyOrder 36 d ∣ 36 := frequencyOrder_dvd_modulus d
  have hmem : frequencyOrder 36 d ∈ (36 : Nat).divisors :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivisors : (36 : Nat).divisors = {1, 2, 3, 4, 6, 9, 12, 18, 36} := by
    decide
  rw [hdivisors] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

private theorem nine_pattern_negation_cover
    (L : Finset (ZMod 36))
    (h : ¬ Z36Card6NineDifferencePatterns L) :
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 3) ∧
      (¬ Z36HasDifferenceOrder L 4) ∧ (¬ Z36HasDifferenceOrder L 6) ∧
      (¬ Z36HasDifferenceOrder L 12)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 3) ∧
      (¬ Z36HasDifferenceOrder L 6) ∧ (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 4) ∧
      (¬ Z36HasDifferenceOrder L 9) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 9) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 4) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 9)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 4) ∧ (¬ Z36HasDifferenceOrder L 6) ∧
      (¬ Z36HasDifferenceOrder L 9) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 6) ∧ (¬ Z36HasDifferenceOrder L 9) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) := by
  unfold Z36Card6NineDifferencePatterns at h
  tauto

private theorem has_order_of_pair
    {L : Finset (ZMod 36)} {x y : ZMod 36} {m : Nat}
    (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y)
    (horder : frequencyOrder 36 (x - y) = m) :
    Z36HasDifferenceOrder L m :=
  ⟨x, hx, y, hy, hne, horder⟩

private theorem pair_order_mem_of_flags
    {L : Finset (ZMod 36)} {U : Finset Nat}
    (h2 : 2 ∈ U ∨ ¬ Z36HasDifferenceOrder L 2)
    (h3 : 3 ∈ U ∨ ¬ Z36HasDifferenceOrder L 3)
    (h4 : 4 ∈ U ∨ ¬ Z36HasDifferenceOrder L 4)
    (h6 : 6 ∈ U ∨ ¬ Z36HasDifferenceOrder L 6)
    (h9 : 9 ∈ U ∨ ¬ Z36HasDifferenceOrder L 9)
    (h12 : 12 ∈ U ∨ ¬ Z36HasDifferenceOrder L 12)
    (h18 : 18 ∈ U ∨ ¬ Z36HasDifferenceOrder L 18)
    (h36 : 36 ∈ U ∨ ¬ Z36HasDifferenceOrder L 36)
    {x y : ZMod 36} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) :
    frequencyOrder 36 (x - y) ∈ U := by
  have hdne : x - y ≠ 0 := sub_ne_zero.mpr hne
  rcases z36_nonzero_order_cases hdne with h | h | h | h | h | h | h | h
  · rcases h2 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h3 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h4 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h6 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h9 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h12 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h18 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim
  · rcases h36 with hm | hn
    · simpa [h] using hm
    · exact (hn (has_order_of_pair hx hy hne h)).elim

private theorem card_le_of_global_coloring
    {k : Nat} (L : Finset (ZMod 36)) (U : Finset Nat)
    (color : ZMod 36 → Fin k)
    (hsep : ∀ x y : ZMod 36, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U → color x ≠ color y)
    (hallowed : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U) :
    L.card ≤ k := by
  have hinj : Set.InjOn color (L : Set (ZMod 36)) := by
    intro x hx y hy hxy
    by_contra hne
    exact (hsep x y hne (hallowed x hx y hy hne)) hxy
  simpa using Finset.card_le_card_of_injOn color
    (s := L) (t := (Finset.univ : Finset (Fin k)))
    (fun _ _ => Finset.mem_univ _) hinj

private theorem card_le_five_of_neighbor_coloring
    (L : Finset (ZMod 36)) (U : Finset Nat)
    (color : ZMod 36 → Fin 4)
    (hsep : ∀ x y : ZMod 36, x ≠ 0 → y ≠ 0 →
      frequencyOrder 36 x ∈ U → frequencyOrder 36 y ∈ U →
      frequencyOrder 36 (x - y) ∈ U → color x ≠ color y)
    (hallowed : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U)
    (hL : L.Nonempty) :
    L.card ≤ 5 := by
  obtain ⟨c, hc⟩ := hL
  let f : ZMod 36 → Fin 4 := fun x => color (x - c)
  have hinj : Set.InjOn f ((L.erase c : Finset (ZMod 36)) : Set (ZMod 36)) := by
    intro x hx y hy hxy
    have hxc : x ≠ c := (Finset.mem_erase.mp hx).1
    have hyc : y ≠ c := (Finset.mem_erase.mp hy).1
    have hxL : x ∈ L := (Finset.mem_erase.mp hx).2
    have hyL : y ∈ L := (Finset.mem_erase.mp hy).2
    by_contra hxyne
    have hsep' := hsep (x - c) (y - c)
      (sub_ne_zero.mpr hxc) (sub_ne_zero.mpr hyc)
      (hallowed x hxL c hc hxc)
      (hallowed y hyL c hc hyc)
      (by simpa only [sub_sub_sub_cancel_right] using
        hallowed x hxL y hyL hxyne)
    exact hsep' hxy
  have hcardErase : (L.erase c).card ≤ 4 := by
    simpa using Finset.card_le_card_of_injOn f
      (s := L.erase c) (t := (Finset.univ : Finset (Fin 4)))
      (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_erase_of_mem hc] at hcardErase
  omega

/-- Every six-element subset of `ZMod 36` has one of the exact nine minimal
difference-order patterns. -/
theorem z36_card6_nine_difference_patterns_structural
    (L : Finset (ZMod 36)) (hcard : L.card = 6) :
    Z36Card6NineDifferencePatterns L := by
  by_contra hnot
  have hL : L.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hcard
    simp at hcard
  rcases nine_pattern_negation_cover L hnot with
    h | h | h | h | h | h | h | h | h
  · have ha := pair_order_mem_of_flags (L := L) (U := U1)
      (Or.inr h.1) (Or.inr h.2.1) (Or.inr h.2.2.1)
      (Or.inr h.2.2.2.1) (Or.inl (by decide)) (Or.inr h.2.2.2.2)
      (Or.inl (by decide)) (Or.inl (by decide))
    have hc := card_le_of_global_coloring L U1 colorU1
      z36_colorU1_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U2)
      (Or.inr h.1) (Or.inr h.2.1) (Or.inl (by decide))
      (Or.inr h.2.2.1) (Or.inl (by decide)) (Or.inl (by decide))
      (Or.inl (by decide)) (Or.inr h.2.2.2)
    have hc := card_le_of_global_coloring L U2 colorU2
      z36_colorU2_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U3)
      (Or.inr h.1) (Or.inl (by decide)) (Or.inr h.2.1)
      (Or.inl (by decide)) (Or.inr h.2.2.1) (Or.inl (by decide))
      (Or.inr h.2.2.2.1) (Or.inr h.2.2.2.2)
    have hc := card_le_of_global_coloring L U3 colorU3
      z36_colorU3_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U4)
      (Or.inr h.1) (Or.inl (by decide)) (Or.inl (by decide))
      (Or.inl (by decide)) (Or.inr h.2.1) (Or.inr h.2.2.1)
      (Or.inr h.2.2.2.1) (Or.inr h.2.2.2.2)
    have hc := card_le_of_global_coloring L U4 colorU4
      z36_colorU4_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U5)
      (Or.inl (by decide)) (Or.inr h.1) (Or.inr h.2.1)
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr h.2.2.1)
      (Or.inr h.2.2.2) (Or.inl (by decide))
    have hc := card_le_five_of_neighbor_coloring L U5 colorU5Neighbor
      z36_colorU5_neighbor_separation ha hL
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U6)
      (Or.inl (by decide)) (Or.inr h.1) (Or.inl (by decide))
      (Or.inl (by decide)) (Or.inr h.2) (Or.inl (by decide))
      (Or.inl (by decide)) (Or.inl (by decide))
    have hc := card_le_of_global_coloring L U6 colorU6
      z36_colorU6_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U7)
      (Or.inl (by decide)) (Or.inr h.1) (Or.inl (by decide))
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
      (Or.inr h.2.1) (Or.inr h.2.2)
    have hc := card_le_of_global_coloring L U7 colorU7
      z36_colorU7_separation ha
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U8)
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr h.1)
      (Or.inr h.2.1) (Or.inr h.2.2.1) (Or.inl (by decide))
      (Or.inr h.2.2.2.1) (Or.inr h.2.2.2.2)
    have hc := card_le_five_of_neighbor_coloring L U8 colorU8Neighbor
      z36_colorU8_neighbor_separation ha hL
    omega
  · have ha := pair_order_mem_of_flags (L := L) (U := U9)
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
      (Or.inr h.1) (Or.inr h.2.1) (Or.inr h.2.2.1)
      (Or.inr h.2.2.2.1) (Or.inr h.2.2.2.2)
    have hc := card_le_of_global_coloring L U9 colorU9
      z36_colorU9_separation ha
    omega

#print axioms z36_card6_nine_difference_patterns_structural

end Fuglede
