import Fuglede.Z180K30ExceptionalProjectiveTraceTransportV88
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Affine covariance of the raw K30 certificate (V90)

This module contains only structural facts about lists in `Z/36Z`.  It is
independent of the generated projective catalogue.  In particular, affine
orbit witnesses can be pushed forward by another unit, and the exact Gram
trace moves a dilation from one marginal to the other.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

@[simp]
theorem affinePoint_eq_mul_add_v90
    (unit translation point : RawPoint) :
    affinePoint unit translation point = unit * point + translation := by
  apply Fin.ext
  simp [affinePoint, Fin.mul_def, Fin.add_def, Nat.add_mod]

@[simp]
theorem affinePoint_comp_v90
    (outer outerTranslation inner innerTranslation point : RawPoint) :
    affinePoint outer outerTranslation
        (affinePoint inner innerTranslation point) =
      affinePoint (outer * inner)
        (affinePoint outer outerTranslation innerTranslation) point := by
  simp only [affinePoint_eq_mul_add_v90, mul_add, mul_assoc, add_assoc]

@[simp]
theorem affineSet_comp_v90
    (outer outerTranslation inner innerTranslation : RawPoint)
    (set : RawSet) :
    affineSet outer outerTranslation
        (affineSet inner innerTranslation set) =
      affineSet (outer * inner)
        (affinePoint outer outerTranslation innerTranslation) set := by
  simp only [affineSet, List.map_map]
  apply List.map_congr_left
  intro point hpoint
  exact affinePoint_comp_v90 outer outerTranslation inner innerTranslation point

theorem units36_mul_mem_v90
    {outer inner : RawPoint}
    (houter : outer ∈ units36) (hinner : inner ∈ units36) :
    outer * inner ∈ units36 := by
  simp [units36] at houter hinner ⊢
  rcases houter with houter | houter | houter | houter | houter | houter |
      houter | houter | houter | houter | houter | houter <;>
    rcases hinner with hinner | hinner | hinner | hinner | hinner | hinner |
      hinner | hinner | hinner | hinner | hinner | hinner <;>
    subst outer <;> subst inner <;> decide

theorem rawSetEqB_affine_forward_v90
    {left right : RawSet} (outer outerTranslation : RawPoint)
    (h : rawSetEqB left right = true) :
    rawSetEqB (affineSet outer outerTranslation left)
      (affineSet outer outerTranslation right) = true := by
  simpa only [affineSet] using
    rawSetEqB_map_v86 (affinePoint outer outerTranslation) h

theorem rawSetEqB_affine_comp_forward_v90
    {representative set : RawSet}
    {inner innerTranslation outer outerTranslation : RawPoint}
    (h : rawSetEqB
      (affineSet inner innerTranslation representative) set = true) :
    rawSetEqB
        (affineSet (outer * inner)
          (affinePoint outer outerTranslation innerTranslation)
          representative)
        (affineSet outer outerTranslation set) = true := by
  have hmapped := rawSetEqB_affine_forward_v90 outer outerTranslation h
  simpa only [affineSet_comp_v90] using hmapped

theorem affineEquivalentB_affine_forward_v90
    (representative set : RawSet)
    (outer outerTranslation : RawPoint)
    (houter : outer ∈ units36)
    (hcovered : affineEquivalentB representative set = true) :
    affineEquivalentB representative
      (affineSet outer outerTranslation set) = true := by
  rw [affineEquivalentB] at hcovered ⊢
  rcases List.any_eq_true.mp hcovered with
    ⟨inner, hinner, hcovered⟩
  rcases List.any_eq_true.mp hcovered with
    ⟨innerTranslation, _htranslation, heq⟩
  apply List.any_eq_true.mpr
  refine ⟨outer * inner, units36_mul_mem_v90 houter hinner, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨affinePoint outer outerTranslation innerTranslation,
    by simp [rawUniverse], ?_⟩
  exact rawSetEqB_affine_comp_forward_v90 heq

theorem orbitCoveredB_affine_forward_v90
    (set : RawSet) (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hcovered : orbitCoveredB set = true) :
    orbitCoveredB (affineSet unit translation set) = true := by
  rw [orbitCoveredB] at hcovered ⊢
  rcases List.any_eq_true.mp hcovered with
    ⟨representative, hrepresentative, hequivalent⟩
  exact List.any_eq_true.mpr
    ⟨representative, hrepresentative,
      affineEquivalentB_affine_forward_v90 representative set
        unit translation hunit hequivalent⟩

@[simp]
theorem cyclicDifference_affine_v90
    (unit translation left right : RawPoint) :
    ((affinePoint unit translation left).val + 36 -
        (affinePoint unit translation right).val) % 36 =
      (unit.val * ((left.val + 36 - right.val) % 36)) % 36 := by
  fin_cases unit <;> simp only [affinePoint] <;> omega

private theorem zetaPower_scale_product_v90
    (unit difference otherDifference : Nat) :
    zetaPower (((unit * difference) % 36) * otherDifference) =
      zetaPower (difference * ((unit * otherDifference) % 36)) := by
  unfold zetaPower
  congr 1
  have hleft :
      ((unit * difference) % 36) * otherDifference ≡
        unit * difference * otherDifference [MOD 36] :=
    (Nat.mod_modEq _ _).mul_right _
  have hright :
      difference * (unit * otherDifference) ≡
        difference * ((unit * otherDifference) % 36) [MOD 36] :=
    (Nat.mod_modEq _ _).symm.mul_left _
  exact hleft.trans ((by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hright) :
      unit * difference * otherDifference ≡
        difference * ((unit * otherDifference) % 36) [MOD 36])

theorem energy_scale_argument_v90
    (V : RawSet) (unit translation : RawPoint) (difference : Nat) :
    energy V ((unit.val * difference) % 36) =
      energy (affineSet unit translation V) difference := by
  unfold energy affineSet
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro v hv
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply, cyclicDifference_affine_v90]
  exact zetaPower_scale_product_v90 unit.val difference
    ((v.val + 36 - w.val) % 36)

theorem gramTraceSquare_affine_covariant_v90
    (U V : RawSet) (unit leftTranslation rightTranslation : RawPoint) :
    gramTraceSquare (affineSet unit leftTranslation U) V =
      gramTraceSquare U (affineSet unit rightTranslation V) := by
  unfold gramTraceSquare affineSet
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro u hu
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply, cyclicDifference_affine_v90]
  exact energy_scale_argument_v90 V unit rightTranslation
    ((u.val + 36 - w.val) % 36)

#print axioms affineSet_comp_v90
#print axioms orbitCoveredB_affine_forward_v90
#print axioms gramTraceSquare_affine_covariant_v90

end Fuglede.Z180K30ExceptionalRawV2
