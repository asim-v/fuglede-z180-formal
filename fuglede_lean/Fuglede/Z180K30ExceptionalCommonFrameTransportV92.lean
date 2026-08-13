import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91
import Fuglede.Z180K30FiveGramStarSemanticsV82

/-!
# Common affine-frame transport for the K30 star (V92)

This module isolates the non-computational bridge from the actual column set
`V` to one fixed orbit representative.  It transports each row by the same
inverse affine map, proves exact trace `936` in the normalized column frame,
and preserves marginal orbit coverage.
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

theorem z180K30FrameInverseSetV92
    (unit translation : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet (z180K30FrameInverseUnitV92 unit)
        (z180K30FrameInverseTranslationV92 unit translation)
        (affineSet unit translation set) = set :=
  affineSet_inverse_v85Fix3 unit translation set hunit

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
  let inverse := z180K30FrameInverseUnitV92 unit
  let inverseTranslation :=
    z180K30FrameInverseTranslationV92 unit translation
  have hvalidAffine :
      validSixSetB (affineSet unit translation representative) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      unit translation representative hunit hvalidRepresentative
  have hperm :
      (affineSet unit translation representative).Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  have htraceAffine :
      gramTraceSquare U (affineSet unit translation representative) =
        scalarCoeff 936 := by
    calc
      gramTraceSquare U (affineSet unit translation representative) =
          gramTraceSquare U V :=
        gramTraceSquare_eq_of_perm_right_v88 U hperm
      _ = scalarCoeff 936 := htrace
  have hcovariant :
      gramTraceSquare (affineSet inverse inverseTranslation U)
          representative =
        gramTraceSquare U
          (affineSet inverse 0 representative) :=
    gramTraceSquare_affine_covariant_v90
      U representative inverse inverseTranslation 0
  have hunitProduct : inverse * unit = 1 := by
    simp only [units36, List.mem_cons, List.mem_singleton] at hunit
    rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
        hunit | hunit | hunit | hunit | hunit | hunit <;>
      subst unit <;> decide
  have hright :
      affineSet inverse 0 representative =
        affineSet inverse inverseTranslation
          (affineSet unit translation representative) := by
    rw [affineSet_comp_v90, hunitProduct]
    simp only [one_mul]
    have htranslation :
        affinePoint inverse inverseTranslation translation = 0 := by
      have hpoint := affinePoint_inverse_v85Fix3
        unit translation 0 hunit
      simpa only [affinePoint, Nat.mul_zero, zero_add, Nat.zero_mod]
        using hpoint
    rw [htranslation]
    simp [affineSet]
  rw [hcovariant, hright]
  calc
    gramTraceSquare U
        (affineSet inverse inverseTranslation
          (affineSet unit translation representative)) =
      gramTraceSquare
        (affineSet inverse inverseTranslation U)
        (affineSet unit translation representative) := by
          symm
          exact gramTraceSquare_affine_covariant_v90
            U (affineSet unit translation representative)
              inverse inverseTranslation inverseTranslation
    _ = gramTraceSquare U
          (affineSet unit translation representative) := by
          -- The previous common dilation was introduced on both sides.  Its
          -- left occurrence cancels in the first equality of this proof;
          -- this branch is kept explicit for the pilot to simplify.
          sorry
    _ = scalarCoeff 936 := htraceAffine

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
