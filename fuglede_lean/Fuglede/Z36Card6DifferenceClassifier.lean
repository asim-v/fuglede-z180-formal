import Fuglede.Z36Card6DifferenceShards

/-!
# Typed endpoint for the sharded `ZMod 36` difference classifier
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem z36_hasDifferenceOrder_of_translate
    (L : Finset (ZMod 36)) (c : ZMod 36) (m : Nat)
    (h : Z36HasDifferenceOrder (L.image fun x => x - c) m) :
    Z36HasDifferenceOrder L m := by
  obtain ⟨x, hx, y, hy, hxy, horder⟩ := h
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨u, hu, v, hv, ?_, ?_⟩
  · intro huv
    exact hxy (by rw [huv])
  · convert horder using 2 <;> abel

private theorem z36_ninePatterns_of_translate
    (L : Finset (ZMod 36)) (c : ZMod 36)
    (h : Z36Card6NineDifferencePatterns (L.image fun x => x - c)) :
    Z36Card6NineDifferencePatterns L := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨z36_hasDifferenceOrder_of_translate L c 2 h.1,
      z36_hasDifferenceOrder_of_translate L c 3 h.2.1,
      z36_hasDifferenceOrder_of_translate L c 6 h.2.2⟩
  · exact Or.inr (Or.inl ⟨z36_hasDifferenceOrder_of_translate L c 2 h.1,
      z36_hasDifferenceOrder_of_translate L c 9 h.2.1,
      z36_hasDifferenceOrder_of_translate L c 18 h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 3 h.1,
       z36_hasDifferenceOrder_of_translate L c 4 h.2.1,
       z36_hasDifferenceOrder_of_translate L c 12 h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 3 h.1,
       z36_hasDifferenceOrder_of_translate L c 9 h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 3 h.1,
       z36_hasDifferenceOrder_of_translate L c 18 h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 3 h.1,
       z36_hasDifferenceOrder_of_translate L c 36 h.2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 4 h.1,
       z36_hasDifferenceOrder_of_translate L c 9 h.2.1,
       z36_hasDifferenceOrder_of_translate L c 36 h.2.2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z36_hasDifferenceOrder_of_translate L c 6 h.1,
       z36_hasDifferenceOrder_of_translate L c 9 h.2.1,
       z36_hasDifferenceOrder_of_translate L c 18 h.2.2⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z36_hasDifferenceOrder_of_translate L c 9 h.1,
       z36_hasDifferenceOrder_of_translate L c 12 h.2.1,
       z36_hasDifferenceOrder_of_translate L c 36 h.2.2⟩)))))))

theorem z36_normalized_card6_nine_difference_patterns
    (K : Finset (ZMod 36)) (hcard : K.card = 6) (hzero : 0 ∈ K) :
    Z36Card6NineDifferencePatterns K := by
  have hcardErase : (K.erase 0).card = 5 := by
    rw [Finset.card_erase_of_mem hzero, hcard]
  have hnonempty : (K.erase 0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcardErase
    simp at hcardErase
  obtain ⟨a, haErase⟩ := hnonempty
  have ha0 : a ≠ 0 := by simpa using (Finset.mem_erase.mp haErase).1
  let S : Finset (ZMod 36) := (K.erase 0).erase a
  have hcardS : S.card = 4 := by
    rw [S, Finset.card_erase_of_mem haErase, hcardErase]
  have hsubsetS : S ⊆ (Finset.univ.erase 0).erase a := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hx0 := Finset.mem_erase.mp hx'.2
    exact Finset.mem_erase.mpr ⟨hx'.1,
      Finset.mem_erase.mpr ⟨hx0.1, Finset.mem_univ x⟩⟩
  have hScandidate : S ∈ z36Card6RemainderCandidates a :=
    z36_mem_remainderCandidates_iff.mpr ⟨hcardS, hsubsetS⟩
  have hraw := z36_card6_difference_shard_dispatch a ha0 ⟨S, hScandidate⟩
  have hinsertA : insert a S = K.erase 0 := by
    exact Finset.insert_erase haErase
  have hinsertZero : insert 0 (K.erase 0) = K :=
    Finset.insert_erase hzero
  rwa [hinsertA, hinsertZero] at hraw

/-- Every six-element subset of `ZMod 36` contains one of the exact nine
minimal difference-order patterns. -/
theorem z36_card6_nine_difference_patterns
    (L : Finset (ZMod 36)) (hcard : L.card = 6) :
    Z36Card6NineDifferencePatterns L := by
  have hnonempty : L.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨c, hc⟩ := hnonempty
  let K : Finset (ZMod 36) := L.image fun x => x - c
  have hinj : Function.Injective (fun x : ZMod 36 => x - c) :=
    fun x y h => sub_right_injective h
  have hcardK : K.card = 6 := by
    rw [K, Finset.card_image_iff.mpr hinj, hcard]
  have hzeroK : 0 ∈ K := by
    rw [K]
    exact Finset.mem_image.mpr ⟨c, hc, sub_self c⟩
  exact z36_ninePatterns_of_translate L c
    (z36_normalized_card6_nine_difference_patterns K hcardK hzeroK)

#print axioms z36_normalized_card6_nine_difference_patterns
#print axioms z36_card6_nine_difference_patterns

end Fuglede
