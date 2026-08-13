import Fuglede.Z180K30ExceptionalProjectiveTraceTransportV88
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

/-!
# Inverse translations for K30 normalization

Translation by `-head` puts zero in a nonempty raw set.  Translation by the
opposite shift is its literal list inverse, so later orbit statements can be
expressed by `List.Perm` without quotienting raw lists.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

@[simp]
theorem affinePoint_one_eq_add_v89 (shift point : RawPoint) :
    affinePoint 1 shift point = shift + point := by
  apply Fin.ext
  simp [affinePoint, Fin.add_def, Nat.add_comm]

@[simp]
theorem affinePoint_neg_comp_v89 (shift point : RawPoint) :
    affinePoint 1 (-shift) (affinePoint 1 shift point) = point := by
  simp [affinePoint_one_eq_add_v89]

@[simp]
theorem affinePoint_comp_neg_v89 (shift point : RawPoint) :
    affinePoint 1 shift (affinePoint 1 (-shift) point) = point := by
  simp [affinePoint_one_eq_add_v89]

@[simp]
theorem affineSet_neg_comp_v89 (shift : RawPoint) (set : RawSet) :
    affineSet 1 (-shift) (affineSet 1 shift set) = set := by
  induction set with
  | nil => rfl
  | cons point tail ih =>
      simp only [affineSet, List.map_cons]
      rw [affinePoint_neg_comp_v89]
      congr 1

@[simp]
theorem affineSet_comp_neg_v89 (shift : RawPoint) (set : RawSet) :
    affineSet 1 shift (affineSet 1 (-shift) set) = set := by
  induction set with
  | nil => rfl
  | cons point tail ih =>
      simp only [affineSet, List.map_cons]
      rw [affinePoint_comp_neg_v89]
      congr 1

theorem mem_affineSet_neg_head_v89
    (head : RawPoint) (tail : List RawPoint) :
    0 ∈ affineSet 1 (-head) (head :: tail) := by
  simp [affineSet]

theorem affineSet_perm_inverse_v89
    (shift : RawPoint) (set normalized : RawSet)
    (hperm : normalized.Perm (affineSet 1 (-shift) set)) :
    set.Perm (affineSet 1 shift normalized) := by
  rw [← affineSet_comp_neg_v89 shift set]
  exact hperm.symm.map (affinePoint 1 shift)

private theorem eraseDups_eq_self_of_nodup_v89 :
    ∀ set : RawSet, set.Nodup → set.eraseDups = set
  | [], _ => by simp
  | head :: tail, hnodup => by
      rw [List.eraseDups_cons]
      have hfiltered :
          tail.filter (fun point => !point == head) = tail := by
        apply List.filter_eq_self.mpr
        intro point hpoint
        have hne : point ≠ head :=
          fun heq => hnodup.notMem (heq ▸ hpoint)
        simp [hne]
      rw [hfiltered, eraseDups_eq_self_of_nodup_v89 tail hnodup.tail]

theorem validSixSetB_of_length_nodup_v89
    {set : RawSet} (hlength : set.length = 6) (hnodup : set.Nodup) :
    validSixSetB set = true := by
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hlength, by simpa [eraseDups_eq_self_of_nodup_v89 _ hnodup]⟩

theorem validSixSetB_affineSet_iff_v89
    (shift : RawPoint) (set : RawSet) :
    validSixSetB (affineSet 1 shift set) = true ↔
      validSixSetB set = true := by
  constructor
  · intro hvalid
    have hlength : set.length = 6 := by
      simpa [validSixSetB, affineSet] using
        (validSixSetB_length_v88 hvalid)
    have hnodupMapped := validSixSetB_nodup_v88 hvalid
    have hnodup : set.Nodup := by
      simpa [affineSet] using List.Nodup.of_map _ hnodupMapped
    simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hlength, by simpa [eraseDups_eq_self_of_nodup_v89 _ hnodup]⟩
  · intro hvalid
    have hlength := validSixSetB_length_v88 hvalid
    have hnodup := validSixSetB_nodup_v88 hvalid
    have hinjective : Function.Injective (affinePoint 1 shift) := by
      intro left right heq
      have := congrArg (affinePoint 1 (-shift)) heq
      simpa using this
    have hnodupMapped : (affineSet 1 shift set).Nodup := by
      exact hnodup.map hinjective
    simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simpa [affineSet] using hlength, ?_⟩
    rw [eraseDups_eq_self_of_nodup_v89 _ hnodupMapped]
    simpa [affineSet] using hlength

#print axioms affineSet_perm_inverse_v89
#print axioms validSixSetB_affineSet_iff_v89

end Fuglede.Z180K30ExceptionalRawV2
