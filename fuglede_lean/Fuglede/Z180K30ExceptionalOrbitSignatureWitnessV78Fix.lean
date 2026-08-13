import Fuglede.Z180K30ExceptionalOrbitSignatureLiteralV78

/-!
# Explicit witnesses for the coupled orbit-signature table (V78 Fix)

Clean replacement for the parser-broken V78 witness draft.  There is no
affine search here: all choices are selected by pattern matching.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30CompatibleRowOrbitV78Fix (o : Fin 8) : Fin 8 :=
  match o with
  | 0 => 7
  | 1 => 7
  | 2 => 4
  | 3 => 7
  | 4 => 2
  | 5 => 7
  | 6 => 7
  | 7 => 7

def z180K30SignatureCandidateV78Fix (o : Fin 8) : RawSet :=
  match o with
  | 0 => [0, 6, 12, 18, 24, 30]
  | 1 => [0, 6, 12, 18, 24, 30]
  | 2 => [0, 12, 15, 18, 30, 33]
  | 3 => [0, 6, 12, 18, 24, 30]
  | 4 => [0, 10, 12, 22, 24, 34]
  | 5 => [0, 6, 12, 18, 24, 30]
  | 6 => [0, 6, 12, 18, 24, 30]
  | 7 => []

theorem z180K30SignatureCandidateV78Fix_mem
    (o : Fin 8) (ho : o ≠ 7) :
    z180K30SignatureCandidateV78Fix o ∈
      z180K30ExceptionalOrbitChoicesV4 o := by
  fin_cases o <;> decide

theorem z180K30SignatureCandidateV78Fix_eq_unit_image
    (o : Fin 8) (ho : o ≠ 7) :
    z180K30StarSignatureV78 o
        (affineSet 1 0
          (z180K30ExceptionalOrbitColumnV4
            (z180K30CompatibleRowOrbitV78Fix o))) =
      z180K30StarSignatureV78 o
        (z180K30SignatureCandidateV78Fix o) := by
  fin_cases o <;> decide

#print axioms z180K30SignatureCandidateV78Fix_mem
#print axioms z180K30SignatureCandidateV78Fix_eq_unit_image

end Fuglede.Z180K30ExceptionalRawV2
