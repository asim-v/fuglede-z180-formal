import Fuglede.Z180K30ExceptionalStarCandidateObstructionV2

/-!
# The exact five-Gram coordinate constraints force the H orbit

This is the proof-only star stage of the finite certificate.  Completeness of
the preceding projective/orbit catalogue is intentionally a separate input.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalOrbitColumn (o : Fin 8) : RawSet :=
  match o with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [0, 10, 12, 18, 24, 30]
  | 2 => [0, 10, 12, 22, 24, 34]
  | 3 => [0, 12, 15, 18, 24, 30]
  | 4 => [0, 12, 15, 18, 30, 33]
  | 5 => [0, 12, 16, 18, 24, 30]
  | 6 => [0, 12, 18, 21, 24, 30]
  | 7 => [0, 6, 12, 18, 24, 30]

def z180K30ExceptionalOrbitChoices (o : Fin 8) : List RawSet :=
  match o with
  | 0 => z180K30ExceptionalSixCosets
  | 1 => z180K30ExceptionalSixCosets
  | 2 => z180K30ExceptionalOrbitTwoChoices
  | 3 => z180K30ExceptionalSixCosets
  | 4 => z180K30ExceptionalOrbitFourChoices
  | 5 => z180K30ExceptionalSixCosets
  | 6 => z180K30ExceptionalSixCosets
  | 7 => []

def z180K30FiveGramCoefficientSum
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat) : Int :=
  gramCoefficientV2 (gram (U 0) V) entry coefficient +
    gramCoefficientV2 (gram (U 1) V) entry coefficient +
    gramCoefficientV2 (gram (U 2) V) entry coefficient +
    gramCoefficientV2 (gram (U 3) V) entry coefficient +
    gramCoefficientV2 (gram (U 4) V) entry coefficient

def Z180K30ExceptionalOrbitStarCoordinates
    (o : Fin 8) (U : Fin 5 -> RawSet) : Prop :=
  match o with
  | 0 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 0) 3 0 = 0
  | 1 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 1) 3 0 = 0
  | 2 => z180K30FiveGramCoefficientSum U
        (z180K30ExceptionalOrbitColumn 2) 2 0 = 0 /\
      z180K30FiveGramCoefficientSum U
        (z180K30ExceptionalOrbitColumn 2) 2 6 = 0
  | 3 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 3) 3 0 = 0
  | 4 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 4) 3 0 = 0
  | 5 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 5) 3 0 = 0
  | 6 => z180K30FiveGramCoefficientSum U
      (z180K30ExceptionalOrbitColumn 6) 2 0 = 0
  | 7 => True

theorem z180_k30_exceptional_star_coordinates_force_H
    (o : Fin 8) (U : Fin 5 -> RawSet)
    (hmem : forall i, U i ∈ z180K30ExceptionalOrbitChoices o)
    (hstar : Z180K30ExceptionalOrbitStarCoordinates o U) :
    o = 7 := by
  fin_cases o
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_zero_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_one_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · exfalso
    have hne := z180_k30_no_fiveGram_coordinate_pair_sum_of_audit_v2
      z180_k30_orbit_two_pairType_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem)
    have hz :
        z180K30FiveGramCoefficientSum U
            [0, 10, 12, 22, 24, 34] 2 0 = 0 /\
          z180K30FiveGramCoefficientSum U
            [0, 10, 12, 22, 24, 34] 2 6 = 0 := by
      simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30ExceptionalOrbitColumn] using hstar
    rcases hne with hne | hne
    · exact hne hz.1
    · exact hne hz.2
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_three_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_four_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_five_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · exfalso
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_six_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoices] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinates,
        z180K30FiveGramCoefficientSum,
        z180K30ExceptionalOrbitColumn] using hstar)
  · rfl

#print axioms z180_k30_exceptional_star_coordinates_force_H

end Fuglede.Z180K30ExceptionalRawV2
