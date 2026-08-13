import Fuglede.Z180K30ExceptionalOrbitSignatureWitnessV78Fix2
import Mathlib.Tactic

/-! # Small fixed-parameter certificates for affine K30 row candidates. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def Z180K30CompatibleAffineCandidateAtV95
    (o : Fin 7) (unit translation : RawPoint) : Prop :=
  ∃ candidate,
    candidate ∈ z180K30ExceptionalOrbitChoicesV4
      (z180K30NonHOrbitV78Fix2 o) ∧
    validSixSetB candidate = true ∧
    rawSetEqB
      (affineSet unit translation
        (z180K30ExceptionalOrbitColumnV4
          (z180K30CompatibleRowOrbitV78Fix2 o)))
      candidate = true

def z180K30CompatibleAffineCandidateAtB_v95
    (o : Fin 7) (unit translation : RawPoint) : Bool :=
  (z180K30ExceptionalOrbitChoicesV4
    (z180K30NonHOrbitV78Fix2 o)).any fun candidate =>
      validSixSetB candidate &&
      rawSetEqB
        (affineSet unit translation
          (z180K30ExceptionalOrbitColumnV4
            (z180K30CompatibleRowOrbitV78Fix2 o)))
        candidate

theorem z180K30CompatibleAffineCandidateAtB_semantics_v95
    (o : Fin 7) (unit translation : RawPoint)
    (h : z180K30CompatibleAffineCandidateAtB_v95
      o unit translation = true) :
    Z180K30CompatibleAffineCandidateAtV95 o unit translation := by
  simp only [z180K30CompatibleAffineCandidateAtB_v95,
    List.any_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨candidate, hmem, hvalid, heq⟩
  exact ⟨candidate, hmem, hvalid, heq⟩

end Fuglede.Z180K30ExceptionalRawV2
