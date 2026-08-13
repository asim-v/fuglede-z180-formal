import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85
import Fuglede.Z180K30ExceptionalRawSetEqSemanticsV85Fix2
import Mathlib.Tactic

/-!
# Reverse affine witness and complete orbit-frame extraction (V85 Fix2)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

@[simp]
theorem affinePoint_inverse_v85Fix2
    (unit translation point : RawPoint)
    (hunit : unit ∈ units36) :
    affinePoint (z180K30UnitInverseV85 unit)
        (affinePoint (z180K30UnitInverseV85 unit) 0
          ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩)
        (affinePoint unit translation point) = point := by
  apply Fin.ext
  simp only [affinePoint]
  have hinverse := z180K30UnitInverseV85_mul hunit
  omega

theorem affineSet_inverse_v85Fix2
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet (z180K30UnitInverseV85 unit)
        (affinePoint (z180K30UnitInverseV85 unit) 0
          ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩)
        (affineSet unit translation set) = set := by
  simp only [affineSet, List.map_map, Function.comp_def,
    affinePoint_inverse_v85Fix2 unit translation _ hunit, List.map_id]

theorem validSixSetB_affine_of_unit_v85Fix2
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36)
    (hvalid : validSixSetB set = true) :
    validSixSetB (affineSet unit translation set) = true := by
  have hinjective : Function.Injective (affinePoint unit translation) := by
    intro left right heq
    have h := congrArg
      (affinePoint (z180K30UnitInverseV85 unit)
        (affinePoint (z180K30UnitInverseV85 unit) 0
          ⟨(36 - translation.val) % 36,
            Nat.mod_lt _ (by norm_num)⟩)) heq
    simpa only [affinePoint_inverse_v85Fix2 unit translation _ hunit] using h
  have hnodup := validSixSetB_nodup_v88 hvalid
  have hlen := validSixSetB_length_v88 hvalid
  have hmapNodup : (affineSet unit translation set).Nodup := by
    exact hnodup.map hinjective
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simpa [affineSet] using hlen, ?_⟩
  have herase : (affineSet unit translation set).eraseDups =
      affineSet unit translation set := by
    exact List.eraseDups_eq_self.mpr hmapNodup
  rw [herase]
  simpa [affineSet] using hlen

theorem reverse_affine_witness_v85Fix2 :
    Fuglede.Z180K30ReverseAffineWitnessV85 := by
  intro V o unit translation hunit hvalidV heq
  let inverse := z180K30UnitInverseV85 unit
  let inverseTranslation : RawPoint :=
    affinePoint inverse 0
      ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩
  have hinverseMem : inverse ∈ units36 :=
    z180K30UnitInverseV85_mem hunit
  have hvalidRep :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 o) = true := by
    fin_cases o <;> decide
  have hvalidAffine :
      validSixSetB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) = true :=
    validSixSetB_affine_of_unit_v85Fix2 unit translation _ hunit hvalidRep
  have heqSymm :
      rawSetEqB V
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) = true :=
    rawSetEqB_symm_of_valid_v85Fix2 hvalidV hvalidAffine heq
  have hmap := rawSetEqB_map_v86
    (affinePoint inverse inverseTranslation) heqSymm
  have hinverseSet :
      affineSet inverse inverseTranslation
          (affineSet unit translation
            (z180K30ExceptionalOrbitColumnV4 o)) =
        z180K30ExceptionalOrbitColumnV4 o := by
    exact affineSet_inverse_v85Fix2 unit translation _ hunit
  unfold affineEquivalentB
  apply List.any_eq_true.mpr
  refine ⟨inverse, hinverseMem, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨inverseTranslation, by simp [rawUniverse], ?_⟩
  simpa only [affineSet, hinverseSet] using hmap

#print axioms reverse_affine_witness_v85Fix2

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

theorem z180_k30_orbitFrameExtraction_v85Fix2 :
    Z180K30OrbitFrameExtractionV84 :=
  z180_k30_orbitFrameExtraction_of_reverse_v85
    reverse_affine_witness_v85Fix2

#print axioms z180_k30_orbitFrameExtraction_v85Fix2

end Fuglede
