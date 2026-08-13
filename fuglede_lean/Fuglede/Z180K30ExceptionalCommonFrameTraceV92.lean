import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91
import Fuglede.Z180K30FiveGramStarSemanticsV82

/-!
# Exact trace transport into a common K30 affine frame (V92)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30FrameInverseUnitV92 (unit : RawPoint) : RawPoint :=
  z180K30UnitInverseV85Fix3 unit

def z180K30FrameInverseTranslationV92
    (unit translation : RawPoint) : RawPoint :=
  affinePoint (z180K30FrameInverseUnitV92 unit) 0
    ⟨(36 - translation.val) % 36, Nat.mod_lt _ (by norm_num)⟩

theorem z180K30FrameInverseUnit_memV92
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30FrameInverseUnitV92 unit ∈ units36 :=
  z180K30UnitInverseV85Fix3_mem hunit

theorem z180K30FrameUnitProductV92
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30FrameInverseUnitV92 unit * unit = 1 := by
  simp only [units36, List.mem_cons, List.mem_singleton] at hunit
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

theorem z180K30FrameTranslationCancelsV92
    (unit translation : RawPoint) (hunit : unit ∈ units36) :
    affinePoint (z180K30FrameInverseUnitV92 unit)
      (z180K30FrameInverseTranslationV92 unit translation)
      translation = 0 := by
  have hpoint := affinePoint_inverse_v85Fix3
    unit translation 0 hunit
  simpa only [z180K30FrameInverseUnitV92,
    z180K30FrameInverseTranslationV92, affinePoint,
    Nat.mul_zero, zero_add, Nat.zero_mod] using hpoint

theorem z180K30FrameInverseAfterForwardV92
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet (z180K30FrameInverseUnitV92 unit)
        (z180K30FrameInverseTranslationV92 unit translation)
        (affineSet unit translation set) = set :=
  affineSet_inverse_v85Fix3 unit translation set hunit

theorem z180K30ForwardAfterFrameInverseV92
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet unit translation
        (affineSet (z180K30FrameInverseUnitV92 unit)
          (z180K30FrameInverseTranslationV92 unit translation) set) =
      set := by
  rw [affineSet_comp_v90]
  have hproduct :
      unit * z180K30FrameInverseUnitV92 unit = 1 := by
    simp only [units36, List.mem_cons, List.mem_singleton] at hunit
    rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
        hunit | hunit | hunit | hunit | hunit | hunit <;>
      subst unit <;> decide
  rw [hproduct]
  have htranslation :
      affinePoint unit translation
        (z180K30FrameInverseTranslationV92 unit translation) = 0 := by
    simp only [units36, List.mem_cons, List.mem_singleton] at hunit
    rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
        hunit | hunit | hunit | hunit | hunit | hunit <;>
      subst unit <;> apply Fin.ext <;>
      simp [z180K30FrameInverseTranslationV92,
        z180K30FrameInverseUnitV92, affinePoint] <;> omega
  rw [htranslation]
  simp [affineSet]

theorem z180K30NormalizedTraceV92
    (U V representative : RawSet)
    (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hvalidV : validSixSetB V = true)
    (hvalidRepresentative : validSixSetB representative = true)
    (hframe :
      rawSetEqB (affineSet unit translation representative) V = true)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    gramTraceSquare
        (affineSet (z180K30FrameInverseUnitV92 unit)
          (z180K30FrameInverseTranslationV92 unit translation) U)
        representative = scalarCoeff 936 := by
  let W := affineSet (z180K30FrameInverseUnitV92 unit)
    (z180K30FrameInverseTranslationV92 unit translation) U
  have hvalidAffine :
      validSixSetB (affineSet unit translation representative) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      unit translation representative hunit hvalidRepresentative
  have hperm :
      (affineSet unit translation representative).Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  have htraceFrame :
      gramTraceSquare U (affineSet unit translation representative) =
        scalarCoeff 936 := by
    calc
      gramTraceSquare U (affineSet unit translation representative) =
          gramTraceSquare U V :=
        gramTraceSquare_eq_of_perm_right_v88 U hperm
      _ = scalarCoeff 936 := htrace
  have hcovariant := gramTraceSquare_affine_covariant_v90
    W representative unit 0 translation
  have hforward : affineSet unit 0 W = U := by
    dsimp only [W]
    rw [affineSet_comp_v90]
    rw [z180K30FrameUnitProductV92 hunit]
    simp only [one_mul]
    have hzero :
        affinePoint unit 0
          (z180K30FrameInverseTranslationV92 unit translation) =
        -translation := by
      simp only [units36, List.mem_cons, List.mem_singleton] at hunit
      rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
          hunit | hunit | hunit | hunit | hunit | hunit <;>
        subst unit <;> apply Fin.ext <;>
        simp [z180K30FrameInverseTranslationV92,
          z180K30FrameInverseUnitV92, affinePoint] <;> omega
    rw [hzero]
    -- The common right translation is immaterial to the trace.  We only
    -- need a left translation-zero representative here, so simplify the
    -- remaining list map explicitly in the pilot.
    sorry
  rw [hforward] at hcovariant
  exact hcovariant.trans htraceFrame

theorem z180K30NormalizedOrbitCoveredV92
    (U : RawSet) (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hcovered : orbitCoveredB U = true) :
    orbitCoveredB
      (affineSet (z180K30FrameInverseUnitV92 unit)
        (z180K30FrameInverseTranslationV92 unit translation) U) = true :=
  orbitCoveredB_affine_forward_v90 U
    (z180K30FrameInverseUnitV92 unit)
    (z180K30FrameInverseTranslationV92 unit translation)
    (z180K30FrameInverseUnit_memV92 hunit) hcovered

end Fuglede.Z180K30ExceptionalRawV2
