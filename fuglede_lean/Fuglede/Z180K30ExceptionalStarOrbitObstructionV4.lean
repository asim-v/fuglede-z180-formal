import Fuglede.Z180K30ExceptionalStarOrbitDefsV4

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_exceptional_star_coordinates_force_H_v4
    (o : Fin 8) (U : Fin 5 -> RawSet)
    (hmem : forall i, List.Mem (U i) (z180K30ExceptionalOrbitChoicesV4 o))
    (hstar : Z180K30ExceptionalOrbitStarCoordinatesV4 o U) :
    o = 7 := by
  have h0 : Not (o = 0) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_zero_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  have h1 : Not (o = 1) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_one_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  have h2 : Not (o = 2) := by
    intro ho
    subst o
    have hne := z180_k30_no_fiveGram_coordinate_pair_sum_of_audit_v2
      z180_k30_orbit_two_pairType_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem)
    have hz :
        z180K30FiveGramCoefficientSumV4 U
            [0, 10, 12, 22, 24, 34] 2 0 = 0 /\
          z180K30FiveGramCoefficientSumV4 U
            [0, 10, 12, 22, 24, 34] 2 6 = 0 := by
      simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30ExceptionalOrbitColumnV4] using hstar
    exact hne.elim (fun hn => hn hz.1) (fun hn => hn hz.2)
  have h3 : Not (o = 3) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_three_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  have h4 : Not (o = 4) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_four_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  have h5 : Not (o = 5) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_five_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  have h6 : Not (o = 6) := by
    intro ho
    subst o
    exact (z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit_v2
      z180_k30_orbit_six_pmSix_audit U
      (by simpa [z180K30ExceptionalOrbitChoicesV4] using hmem))
      (by simpa [Z180K30ExceptionalOrbitStarCoordinatesV4,
        z180K30FiveGramCoefficientSumV4,
        z180K30ExceptionalOrbitColumnV4] using hstar)
  apply Fin.ext
  omega

#print axioms z180_k30_exceptional_star_coordinates_force_H_v4

end Fuglede.Z180K30ExceptionalRawV2
