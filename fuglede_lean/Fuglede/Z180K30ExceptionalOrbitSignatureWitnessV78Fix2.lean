import Fuglede.Z180K30ExceptionalOrbitSignatureLiteralV78

/-!
# Explicit non-H witnesses for the coupled orbit-signature table (V78 Fix2)

The orbit is indexed by `Fin 7`, so the impossible H branch is absent from
the type and every proof is a direct finite reduction.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30NonHOrbitV78Fix2 (o : Fin 7) : Fin 8 :=
  ⟨o.val, Nat.lt_trans o.isLt (by norm_num)⟩

def z180K30CompatibleRowOrbitV78Fix2 (o : Fin 7) : Fin 8 :=
  match o with
  | 0 => 7
  | 1 => 7
  | 2 => 4
  | 3 => 7
  | 4 => 2
  | 5 => 7
  | 6 => 7

def z180K30SignatureCandidateV78Fix2 (o : Fin 7) : RawSet :=
  match o with
  | 0 => [0, 6, 12, 18, 24, 30]
  | 1 => [0, 6, 12, 18, 24, 30]
  | 2 => [0, 12, 15, 18, 30, 33]
  | 3 => [0, 6, 12, 18, 24, 30]
  | 4 => [0, 10, 12, 22, 24, 34]
  | 5 => [0, 6, 12, 18, 24, 30]
  | 6 => [0, 6, 12, 18, 24, 30]

theorem z180K30SignatureCandidateV78Fix2_mem (o : Fin 7) :
    z180K30SignatureCandidateV78Fix2 o ∈
      z180K30ExceptionalOrbitChoicesV4
        (z180K30NonHOrbitV78Fix2 o) := by
  fin_cases o <;> decide

theorem z180K30SignatureCandidateV78Fix2_eq_unit_image (o : Fin 7) :
    z180K30StarSignatureV78 (z180K30NonHOrbitV78Fix2 o)
        (affineSet 1 0
          (z180K30ExceptionalOrbitColumnV4
            (z180K30CompatibleRowOrbitV78Fix2 o))) =
      z180K30StarSignatureV78 (z180K30NonHOrbitV78Fix2 o)
        (z180K30SignatureCandidateV78Fix2 o) := by
  fin_cases o <;> decide

#print axioms z180K30SignatureCandidateV78Fix2_mem
#print axioms z180K30SignatureCandidateV78Fix2_eq_unit_image

end Fuglede.Z180K30ExceptionalRawV2
