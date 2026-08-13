import Fuglede.Z180K30ExceptionalFramedStarInterfacesV84
import Mathlib.Tactic

/-!
# Boolean orbit witnesses and explicit inverses modulo 36 (V85)

This module supplies the low-cost structural part of the framed catalogue:
unpacking `orbitCoveredB`, identifying its literal representative, and
recording inverse units.  The remaining set-equivalence orientation is kept
as one small reusable covariance lemma.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30UnitInverseV85 (unit : RawPoint) : RawPoint :=
  match unit.val with
  | 1 => 1
  | 5 => 29
  | 7 => 31
  | 11 => 23
  | 13 => 25
  | 17 => 17
  | 19 => 19
  | 23 => 11
  | 25 => 13
  | 29 => 5
  | 31 => 7
  | 35 => 35
  | _ => 1

theorem z180K30UnitInverseV85_mem
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30UnitInverseV85 unit ∈ units36 := by
  simp only [units36, List.mem_cons, List.mem_singleton] at hunit ⊢
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

theorem z180K30UnitInverseV85_mul
    {unit : RawPoint} (hunit : unit ∈ units36) :
    (z180K30UnitInverseV85 unit).val * unit.val % 36 = 1 := by
  simp only [units36, List.mem_cons, List.mem_singleton] at hunit
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

/-- The literal V4 orbit table is exactly the raw-core representative list. -/
theorem orbitRepresentative_mem_iff_v85
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

/-- Raw Boolean coverage exposes the forward affine presentation. -/
theorem orbitCoveredB_forward_witness_v85
    {V : RawSet} (hcovered : orbitCoveredB V = true) :
    ∃ o : Fin 8, ∃ unit translation : RawPoint,
      unit ∈ units36 ∧
      rawSetEqB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4 o)) V = true := by
  simp only [orbitCoveredB, List.any_eq_true] at hcovered
  rcases hcovered with ⟨representative, hrep, hequiv⟩
  rcases (orbitRepresentative_mem_iff_v85 representative).1 hrep with
    ⟨o, rfl⟩
  simp only [affineEquivalentB, List.any_eq_true] at hequiv
  rcases hequiv with ⟨unit, hunit, hequiv⟩
  rcases hequiv with ⟨translation, _htranslation, heq⟩
  exact ⟨o, unit, translation, hunit, heq⟩

#print axioms z180K30UnitInverseV85_mul
#print axioms orbitCoveredB_forward_witness_v85

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

/-- Exact remaining set-theoretic orientation lemma.  It is deliberately
separated from Boolean witness extraction so it can be proved once using
`rawSetEqB` semantics and the explicit inverse unit above. -/
def Z180K30ReverseAffineWitnessV85 : Prop :=
  ∀ V : RawSet, ∀ o : Fin 8, ∀ unit translation : RawPoint,
    unit ∈ units36 → validSixSetB V = true →
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4 o)) V = true →
    affineEquivalentB V
      (z180K30ExceptionalOrbitColumnV4 o) = true

theorem z180_k30_orbitFrameExtraction_of_reverse_v85
    (hreverse : Z180K30ReverseAffineWitnessV85) :
    Z180K30OrbitFrameExtractionV84 := by
  intro V hvalid hcovered
  rcases orbitCoveredB_forward_witness_v85 hcovered with
    ⟨o, unit, translation, hunit, heq⟩
  exact ⟨
    { o := o
      unit := unit
      translation := translation
      unit_mem := hunit
      representative_to_V := heq
      V_to_representative := hreverse V o unit translation
        hunit hvalid heq }
  ⟩

#print axioms z180_k30_orbitFrameExtraction_of_reverse_v85

end Fuglede
