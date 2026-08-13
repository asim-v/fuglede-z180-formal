import Fuglede.Z180K30ExceptionalFramedStarInterfacesV84Fix2
import Fuglede.Z180K30ExceptionalOrbitFrameCoreV85Fix3

/-! # Complete constructive orbit-frame extraction (V85 Fix3) -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem orbitRepresentative_mem_iff_v85Fix3
    (representative : RawSet) :
    representative ∈ orbitRepresentatives ↔
      ∃ o : Fin 8,
        representative = z180K30ExceptionalOrbitColumnV4 o := by
  constructor
  · intro h
    simp only [orbitRepresentatives, List.mem_cons,
      List.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h
    · exact ⟨0, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨1, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨2, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨3, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨4, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨5, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨6, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
    · exact ⟨7, by simpa [z180K30ExceptionalOrbitColumnV4] using h⟩
  · rintro ⟨o, rfl⟩
    fin_cases o <;> simp [orbitRepresentatives,
      z180K30ExceptionalOrbitColumnV4]

theorem orbitCoveredB_forward_witness_v85Fix3
    {V : RawSet} (hcovered : orbitCoveredB V = true) :
    ∃ o : Fin 8, ∃ unit translation : RawPoint,
      unit ∈ units36 ∧
      rawSetEqB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) V = true := by
  simp only [orbitCoveredB, List.any_eq_true] at hcovered
  rcases hcovered with ⟨representative, hrep, hequiv⟩
  rcases (orbitRepresentative_mem_iff_v85Fix3 representative).1 hrep with
    ⟨o, rfl⟩
  simp only [affineEquivalentB, List.any_eq_true] at hequiv
  rcases hequiv with ⟨unit, hunit, hequiv⟩
  rcases hequiv with ⟨translation, _htranslation, heq⟩
  exact ⟨o, unit, translation, hunit, heq⟩

theorem reverse_affine_witness_v85Fix3
    (V : RawSet) (o : Fin 8) (unit translation : RawPoint)
    (hunit : unit ∈ units36) (hvalidV : validSixSetB V = true)
    (heq : rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 o)) V = true) :
    affineEquivalentB V
      (z180K30ExceptionalOrbitColumnV4 o) = true := by
  let inverse := z180K30UnitInverseV85Fix3 unit
  let inverseTranslation : RawPoint :=
    affinePoint inverse 0
      ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩
  have hinverseMem : inverse ∈ units36 :=
    z180K30UnitInverseV85Fix3_mem hunit
  have hvalidRep :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 o) = true := by
    fin_cases o <;> decide
  have hvalidAffine :
      validSixSetB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) = true :=
    validSixSetB_affine_of_unit_v85Fix3 unit translation _ hunit hvalidRep
  have heqSymm :
      rawSetEqB V
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) = true :=
    rawSetEqB_symm_of_valid_v85Fix2 hvalidAffine hvalidV heq
  have hmap := rawSetEqB_map_v86
    (affinePoint inverse inverseTranslation) heqSymm
  have hinverseSet :
      affineSet inverse inverseTranslation
          (affineSet unit translation
            (z180K30ExceptionalOrbitColumnV4 o)) =
        z180K30ExceptionalOrbitColumnV4 o :=
    affineSet_inverse_v85Fix3 unit translation _ hunit
  change rawSetEqB
      (affineSet inverse inverseTranslation V)
      (affineSet inverse inverseTranslation
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o))) = true at hmap
  rw [hinverseSet] at hmap
  unfold affineEquivalentB
  apply List.any_eq_true.mpr
  refine ⟨inverse, hinverseMem, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨inverseTranslation, by simp [rawUniverse], hmap⟩

#print axioms reverse_affine_witness_v85Fix3

structure Z180K30ForwardOrbitFrameWitnessV85Fix3 (V : RawSet) where
  o : Fin 8
  unit : RawPoint
  translation : RawPoint
  unit_mem : unit ∈ units36
  representative_to_V :
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 o)) V = true

theorem orbitCoveredB_forward_witness_nonempty_v85Fix3
    {V : RawSet} (hcovered : orbitCoveredB V = true) :
    Nonempty (Z180K30ForwardOrbitFrameWitnessV85Fix3 V) := by
  rcases orbitCoveredB_forward_witness_v85Fix3 hcovered with
    ⟨o, unit, translation, hunit, heq⟩
  exact ⟨
    { o := o
      unit := unit
      translation := translation
      unit_mem := hunit
      representative_to_V := heq }⟩

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable def z180_k30_orbitFrameExtraction_v85Fix3 :
    Z180K30OrbitFrameExtractionV84Fix2 := by
  classical
  intro V hvalid hcovered
  let forward := Classical.choice
    (orbitCoveredB_forward_witness_nonempty_v85Fix3 hcovered)
  exact
    { o := forward.o
      unit := forward.unit
      translation := forward.translation
      unit_mem := forward.unit_mem
      representative_to_V := forward.representative_to_V
      V_to_representative := reverse_affine_witness_v85Fix3
        V forward.o forward.unit forward.translation
          forward.unit_mem hvalid forward.representative_to_V }

#print axioms z180_k30_orbitFrameExtraction_v85Fix3

end Fuglede
