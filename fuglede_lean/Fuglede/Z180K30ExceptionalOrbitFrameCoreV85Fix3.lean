import Fuglede.Z180K30ExceptionalStarOrbitDefsV4
import Fuglede.Z180K30ExceptionalRawSetEqSemanticsV85Fix2
import Mathlib.Tactic

/-! # Constructive affine-frame arithmetic (V85 Fix3) -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30UnitInverseV85Fix3 (unit : RawPoint) : RawPoint :=
  match unit.val with
  | 1 => 1 | 5 => 29 | 7 => 31 | 11 => 23
  | 13 => 25 | 17 => 17 | 19 => 19 | 23 => 11
  | 25 => 13 | 29 => 5 | 31 => 7 | 35 => 35
  | _ => 1

theorem z180K30UnitInverseV85Fix3_mem
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30UnitInverseV85Fix3 unit ∈ units36 := by
  simp only [units36, List.mem_cons, List.not_mem_nil, or_false] at hunit ⊢
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

@[simp]
theorem affinePoint_inverse_v85Fix3
    (unit translation point : RawPoint)
    (hunit : unit ∈ units36) :
    affinePoint (z180K30UnitInverseV85Fix3 unit)
        (affinePoint (z180K30UnitInverseV85Fix3 unit) 0
          ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩)
        (affinePoint unit translation point) = point := by
  simp only [units36, List.mem_cons, List.not_mem_nil, or_false] at hunit
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> apply Fin.ext <;>
    simp [affinePoint, z180K30UnitInverseV85Fix3] <;> omega

theorem affineSet_inverse_v85Fix3
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet (z180K30UnitInverseV85Fix3 unit)
        (affinePoint (z180K30UnitInverseV85Fix3 unit) 0
          ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩)
        (affineSet unit translation set) = set := by
  induction set with
  | nil => rfl
  | cons point tail ih =>
      simp only [affineSet, List.map_cons]
      rw [affinePoint_inverse_v85Fix3 unit translation point hunit]
      exact congrArg (List.cons point) ih

private theorem eraseDups_eq_self_of_nodup_v85Fix3
    {set : RawSet} (h : set.Nodup) : set.eraseDups = set := by
  induction set with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at h
      have hfilter : (tail.filter fun point => !point == head) = tail := by
        apply List.filter_eq_self.mpr
        intro point hpoint
        have hne : point ≠ head := by
          intro heq
          apply h.1
          simpa [heq] using hpoint
        simp [hne]
      rw [List.eraseDups_cons, hfilter, ih h.2]

theorem validSixSetB_affine_of_unit_v85Fix3
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36)
    (hvalid : validSixSetB set = true) :
    validSixSetB (affineSet unit translation set) = true := by
  have hinjective : Function.Injective (affinePoint unit translation) := by
    intro left right heq
    have h := congrArg
      (affinePoint (z180K30UnitInverseV85Fix3 unit)
        (affinePoint (z180K30UnitInverseV85Fix3 unit) 0
          ⟨(36 - translation.val) % 36,
            Nat.mod_lt _ (by norm_num)⟩)) heq
    simpa only [affinePoint_inverse_v85Fix3 unit translation _ hunit] using h
  have hnodup := validSixSetB_nodup_v88 hvalid
  have hlen := validSixSetB_length_v88 hvalid
  have hmapNodup : (affineSet unit translation set).Nodup :=
    hnodup.map hinjective
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simpa [affineSet] using hlen, ?_⟩
  rw [eraseDups_eq_self_of_nodup_v85Fix3 hmapNodup]
  simpa [affineSet] using hlen

#print axioms affineSet_inverse_v85Fix3
#print axioms validSixSetB_affine_of_unit_v85Fix3

end Fuglede.Z180K30ExceptionalRawV2
