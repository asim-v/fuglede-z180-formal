import Fuglede.Z36Card6DifferenceCore
import Mathlib.Tactic

/-! Shared non-enumerative lemmas for the structural difference classifier. -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_nonzero_order_cases {d : ZMod 36} (hd : d ≠ 0) :
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

theorem z36_has_order_of_pair
    {L : Finset (ZMod 36)} {x y : ZMod 36} {m : Nat}
    (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y)
    (horder : frequencyOrder 36 (x - y) = m) :
    Z36HasDifferenceOrder L m :=
  ⟨x, hx, y, hy, hne, horder⟩

theorem z36_pair_order_mem_of_flags
    {L : Finset (ZMod 36)} {U : Finset Nat}
    (h2 : 2 ∈ U ∨ ¬ Z36HasDifferenceOrder L 2)
    (h3 : 3 ∈ U ∨ ¬ Z36HasDifferenceOrder L 3)
    (h4 : 4 ∈ U ∨ ¬ Z36HasDifferenceOrder L 4)
    (h6 : 6 ∈ U ∨ ¬ Z36HasDifferenceOrder L 6)
    (h9 : 9 ∈ U ∨ ¬ Z36HasDifferenceOrder L 9)
    (h12 : 12 ∈ U ∨ ¬ Z36HasDifferenceOrder L 12)
    (h18 : 18 ∈ U ∨ ¬ Z36HasDifferenceOrder L 18)
    (h36 : 36 ∈ U ∨ ¬ Z36HasDifferenceOrder L 36)
    (x : ZMod 36) (hx : x ∈ L) (y : ZMod 36) (hy : y ∈ L) (hne : x ≠ y) :
    frequencyOrder 36 (x - y) ∈ U := by
  have hdne : x - y ≠ 0 := sub_ne_zero.mpr hne
  rcases z36_nonzero_order_cases hdne with h | h | h | h | h | h | h | h
  · rcases h2 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h3 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h4 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h6 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h9 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h12 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h18 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim
  · rcases h36 with hm | hn
    · simpa [h] using hm
    · exact (hn (z36_has_order_of_pair hx hy hne h)).elim

theorem z36_card_le_of_global_coloring
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

theorem z36_card_le_five_of_neighbor_coloring
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

end Fuglede
