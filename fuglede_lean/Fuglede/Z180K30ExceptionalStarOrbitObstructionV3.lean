import Fuglede.Z180K30ExceptionalStarCandidateObstructionV2

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalOrbitColumnV3 (o : Fin 8) : RawSet :=
  match o with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [0, 10, 12, 18, 24, 30]
  | 2 => [0, 10, 12, 22, 24, 34]
  | 3 => [0, 12, 15, 18, 24, 30]
  | 4 => [0, 12, 15, 18, 30, 33]
  | 5 => [0, 12, 16, 18, 24, 30]
  | 6 => [0, 12, 18, 21, 24, 30]
  | 7 => [0, 6, 12, 18, 24, 30]

def z180K30ExceptionalOrbitChoicesV3 (o : Fin 8) : List RawSet :=
  match o with
  | 0 => z180K30ExceptionalSixCosets
  | 1 => z180K30ExceptionalSixCosets
  | 2 => z180K30ExceptionalOrbitTwoChoices
  | 3 => z180K30ExceptionalSixCosets
  | 4 => z180K30ExceptionalOrbitFourChoices
  | 5 => z180K30ExceptionalSixCosets
  | 6 => z180K30ExceptionalSixCosets
  | 7 => []

def z180K30FiveGramCoefficientSumV3
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat) : Int :=
  gramCoefficientV2 (gram (U 0) V) entry coefficient +
    gramCoefficientV2 (gram (U 1) V) entry coefficient +
    gramCoefficientV2 (gram (U 2) V) entry coefficient +
    gramCoefficientV2 (gram (U 3) V) entry coefficient +
    gramCoefficientV2 (gram (U 4) V) entry coefficient

def Z180K30ExceptionalOrbitStarCoordinatesV3
    (o : Fin 8) (U : Fin 5 -> RawSet) : Prop :=
  match o with
  | 0 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 0) 3 0 = 0
  | 1 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 1) 3 0 = 0
  | 2 => z180K30FiveGramCoefficientSumV3 U
        (z180K30ExceptionalOrbitColumnV3 2) 2 0 = 0 /\
      z180K30FiveGramCoefficientSumV3 U
        (z180K30ExceptionalOrbitColumnV3 2) 2 6 = 0
  | 3 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 3) 3 0 = 0
  | 4 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 4) 3 0 = 0
  | 5 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 5) 3 0 = 0
  | 6 => z180K30FiveGramCoefficientSumV3 U
      (z180K30ExceptionalOrbitColumnV3 6) 2 0 = 0
  | 7 => True

theorem z180_k30_exceptional_star_coordinates_force_H_v3
    (o : Fin 8) (U : Fin 5 -> RawSet)
    (hmem : forall i, List.Mem (U i) (z180K30ExceptionalOrbitChoicesV3 o))
    (hstar : Z180K30ExceptionalOrbitStarCoordinatesV3 o U) :
    o = 7 := by
  have h0 : o != 0 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_zero_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  have h1 : o != 1 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_one_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  have h2 : o != 2 := by
    intro ho
    subst o
    have hne := z180_k30_no_fiveGram_coordinate_pair_sum_of_audit_v2
      z180_k30_orbit_two_pairType_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem)
    have hz :
        z180K30FiveGramCoefficientSumV3 U
            [0, 10, 12, 22, 24, 34] 2 0 = 0 /\
          z180K30FiveGramCoefficientSumV3 U
            [0, 10, 12, 22, 24, 34] 2 6 = 0 := by
      simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30ExceptionalOrbitColumnV3] using hstar
    exact hne.elim (fun hn => hn hz.1) (fun hn => hn hz.2)
  have h3 : o != 3 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_three_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  have h4 : o != 4 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_four_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  have h5 : o != 5 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_five_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  have h6 : o != 6 := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_six_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV3] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV3,
        z180K30FiveGramCoefficientSumV3,
        z180K30ExceptionalOrbitColumnV3] using hstar)
  apply Fin.ext
  omega

#print axioms z180_k30_exceptional_star_coordinates_force_H_v3

end Fuglede.Z180K30ExceptionalRawV2
