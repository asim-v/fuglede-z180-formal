import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Permutation and translation transport for K30 projective marginals

These lemmas are independent of the generated literal catalogue.  They
transport an explicit affine-orbit certificate through the two operations
used by projective normalization: reordering a raw set and translating it.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem rawSetEqB_map_v86
    (f : RawPoint → RawPoint) {left right : RawSet}
    (h : rawSetEqB left right = true) :
    rawSetEqB (left.map f) (right.map f) = true := by
  simp only [rawSetEqB, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨by simpa using h.1, ?_⟩
  apply List.all_eq_true.mpr
  intro point hpoint
  rcases List.mem_map.mp hpoint with ⟨source, hsource, rfl⟩
  apply decide_eq_true
  apply List.mem_map.mpr
  exact ⟨source,
    of_decide_eq_true ((List.all_eq_true.mp h.2) source hsource), rfl⟩

theorem rawSetEqB_right_perm_v86
    (left : RawSet) {right right' : RawSet}
    (hperm : right.Perm right') :
    rawSetEqB left right = rawSetEqB left right' := by
  have hall :
      left.all (fun point => decide (point ∈ right)) =
        left.all (fun point => decide (point ∈ right')) := by
    apply List.all_congr rfl
    intro point
    exact decide_eq_decide.mpr hperm.mem_iff
  simp only [rawSetEqB, hperm.length_eq, hall]

theorem affineEquivalentB_right_perm_v86
    (left : RawSet) {right right' : RawSet}
    (hperm : right.Perm right') :
    affineEquivalentB left right = affineEquivalentB left right' := by
  unfold affineEquivalentB
  apply List.any_congr rfl
  intro unit
  apply List.any_congr rfl
  intro translation
  exact rawSetEqB_right_perm_v86 _ hperm

theorem orbitCoveredB_eq_of_perm_v86
    {set set' : RawSet} (hperm : set.Perm set') :
    orbitCoveredB set = orbitCoveredB set' := by
  unfold orbitCoveredB
  apply List.any_congr rfl
  intro representative
  exact affineEquivalentB_right_perm_v86 representative hperm

@[simp]
theorem affinePoint_translation_comp_v86
    (unit translation shift point : RawPoint) :
    affinePoint 1 shift (affinePoint unit translation point) =
      affinePoint unit (affinePoint 1 shift translation) point := by
  apply Fin.ext
  simp [affinePoint, Nat.add_assoc]

theorem affineEquivalentB_translate_right_v86
    (representative set : RawSet) (shift : RawPoint)
    (hcovered : affineEquivalentB representative set = true) :
    affineEquivalentB representative (affineSet 1 shift set) = true := by
  rw [affineEquivalentB] at hcovered ⊢
  rcases List.any_eq_true.mp hcovered with ⟨unit, hunit, hcovered⟩
  rcases List.any_eq_true.mp hcovered with
    ⟨translation, _htranslation, hset⟩
  apply List.any_eq_true.mpr
  refine ⟨unit, hunit, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨affinePoint 1 shift translation, by simp [rawUniverse], ?_⟩
  have hmap := rawSetEqB_map_v86 (affinePoint 1 shift) hset
  have hcomp :
      (affinePoint 1 shift ∘ affinePoint unit translation) =
        affinePoint unit (affinePoint 1 shift translation) := by
    funext point
    exact affinePoint_translation_comp_v86 unit translation shift point
  simpa only [affineSet, List.map_map, hcomp] using hmap

theorem orbitCoveredB_translate_v86
    (set : RawSet) (shift : RawPoint)
    (hcovered : orbitCoveredB set = true) :
    orbitCoveredB (affineSet 1 shift set) = true := by
  rw [orbitCoveredB] at hcovered ⊢
  rcases List.any_eq_true.mp hcovered with
    ⟨representative, hrepresentative, hequivalent⟩
  exact List.any_eq_true.mpr
    ⟨representative, hrepresentative,
      affineEquivalentB_translate_right_v86
        representative set shift hequivalent⟩

#print axioms orbitCoveredB_eq_of_perm_v86
#print axioms orbitCoveredB_translate_v86

end Fuglede.Z180K30ExceptionalRawV2
