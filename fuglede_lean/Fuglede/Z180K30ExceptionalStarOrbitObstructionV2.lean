import Fuglede.Z180K30ExceptionalStarCandidateObstructionV2

/-!
# The exact five-Gram coordinate constraints force the H orbit

This is the proof-only star stage of the finite certificate. Completeness of
the preceding projective/orbit catalogue is intentionally a separate input.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalOrbitColumnV2 (o : Fin 8) : RawSet :=
  match o with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [0, 10, 12, 18, 24, 30]
  | 2 => [0, 10, 12, 22, 24, 34]
  | 3 => [0, 12, 15, 18, 24, 30]
  | 4 => [0, 12, 15, 18, 30, 33]
  | 5 => [0, 12, 16, 18, 24, 30]
  | 6 => [0, 12, 18, 21, 24, 30]
  | 7 => [0, 6, 12, 18, 24, 30]

def z180K30ExceptionalOrbitChoicesV2 (o : Fin 8) : List RawSet :=
  match o with
  | 0 => z180K30ExceptionalSixCosets
  | 1 => z180K30ExceptionalSixCosets
  | 2 => z180K30ExceptionalOrbitTwoChoices
  | 3 => z180K30ExceptionalSixCosets
  | 4 => z180K30ExceptionalOrbitFourChoices
  | 5 => z180K30ExceptionalSixCosets
  | 6 => z180K30ExceptionalSixCosets
  | 7 => []

def z180K30FiveGramCoefficientSumV2
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat) : Int :=
  gramCoefficientV2 (gram (U 0) V) entry coefficient +
    gramCoefficientV2 (gram (U 1) V) entry coefficient +
    gramCoefficientV2 (gram (U 2) V) entry coefficient +
    gramCoefficientV2 (gram (U 3) V) entry coefficient +
    gramCoefficientV2 (gram (U 4) V) entry coefficient

def Z180K30ExceptionalOrbitStarCoordinatesV2
    (o : Fin 8) (U : Fin 5 -> RawSet) : Prop :=
  match o with
  | 0 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 0) 3 0 = 0
  | 1 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 1) 3 0 = 0
  | 2 => z180K30FiveGramCoefficientSumV2 U
        (z180K30ExceptionalOrbitColumnV2 2) 2 0 = 0 /\
      z180K30FiveGramCoefficientSumV2 U
        (z180K30ExceptionalOrbitColumnV2 2) 2 6 = 0
  | 3 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 3) 3 0 = 0
  | 4 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 4) 3 0 = 0
  | 5 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 5) 3 0 = 0
  | 6 => z180K30FiveGramCoefficientSumV2 U
      (z180K30ExceptionalOrbitColumnV2 6) 2 0 = 0
  | 7 => True

theorem z180_k30_exceptional_star_coordinates_force_H_v2
    (o : Fin 8) (U : Fin 5 -> RawSet)
    (hmem : forall i, List.Mem (U i) (z180K30ExceptionalOrbitChoicesV2 o))
    (hstar : Z180K30ExceptionalOrbitStarCoordinatesV2 o U) :
    o = 7 := by
  fin_cases o
  all_goals
    first
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_zero_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_one_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | exact False.elim (by
        have hne := z180_k30_no_fiveGram_coordinate_pair_sum_of_audit_v2
          z180_k30_orbit_two_pairType_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem)
        have hz :
            z180K30FiveGramCoefficientSumV2 U
                [0, 10, 12, 22, 24, 34] 2 0 = 0 /\
              z180K30FiveGramCoefficientSumV2 U
                [0, 10, 12, 22, 24, 34] 2 6 = 0 := by
          simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30ExceptionalOrbitColumnV2] using hstar
        exact hne.elim (fun hn => hn hz.1) (fun hn => hn hz.2))
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_three_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_four_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_five_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | exact False.elim
        ((z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
          z180_k30_orbit_six_pmSix_audit U
          (by simpa [z180K30ExceptionalOrbitChoicesV2] using hmem))
          (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV2,
            z180K30FiveGramCoefficientSumV2,
            z180K30ExceptionalOrbitColumnV2] using hstar))
    | rfl

#print axioms z180_k30_exceptional_star_coordinates_force_H_v2

end Fuglede.Z180K30ExceptionalRawV2
