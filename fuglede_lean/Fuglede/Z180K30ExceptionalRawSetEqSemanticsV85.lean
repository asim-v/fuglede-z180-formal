import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Set semantics of the raw six-point Boolean equality (V85)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem rawSetEqB_length_eq_v85
    {left right : RawSet} (h : rawSetEqB left right = true) :
    left.length = right.length := by
  simp only [rawSetEqB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem rawSetEqB_subset_v85
    {left right : RawSet} (h : rawSetEqB left right = true) :
    ∀ point ∈ left, point ∈ right := by
  simp only [rawSetEqB, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem rawSetEqB_symm_of_nodup_v85
    {left right : RawSet}
    (hleft : left.Nodup) (hright : right.Nodup)
    (h : rawSetEqB left right = true) :
    rawSetEqB right left = true := by
  have hlen := rawSetEqB_length_eq_v85 h
  have hsubset := rawSetEqB_subset_v85 h
  have hcardLeft : left.toFinset.card = left.length := by
    simpa using List.toFinset_card_of_nodup hleft
  have hcardRight : right.toFinset.card = right.length := by
    simpa using List.toFinset_card_of_nodup hright
  have hfinsetSubset : left.toFinset ⊆ right.toFinset := by
    intro point hp
    rw [List.mem_toFinset] at hp ⊢
    exact hsubset point hp
  have hfinsetEq : left.toFinset = right.toFinset := by
    apply Finset.eq_of_subset_of_card_le hfinsetSubset
    simpa [hcardLeft, hcardRight, hlen]
  apply Bool.and_eq_true.mpr
  refine ⟨?_, ?_⟩
  · exact beq_iff_eq.mpr hlen.symm
  · apply List.all_eq_true.mpr
    intro point hp
    apply decide_eq_true_eq.mpr
    rw [← List.mem_toFinset, ← hfinsetEq, List.mem_toFinset]
    exact hp

theorem validSixSetB_nodup_v85
    {set : RawSet} (hvalid : validSixSetB set = true) : set.Nodup := by
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq] at hvalid
  have hlen : set.length = 6 := hvalid.1
  have herase : set.eraseDups.length = 6 := hvalid.2
  exact (List.nodup_iff_count_le_one).2 fun point => by
    by_contra hnot
    have htwo : 2 ≤ set.count point := by omega
    have hstrict : set.eraseDups.length < set.length := by
      rw [List.length_eraseDups]
      sorry
    omega

end Fuglede.Z180K30ExceptionalRawV2
