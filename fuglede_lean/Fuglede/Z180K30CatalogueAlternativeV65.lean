import Fuglede.Z180K30ExceptionalStarOrbitObstructionV5
import Fuglede.Z180K30ExceptionalHGramWitness

namespace Fuglede.Z180K30ExceptionalRawV2

structure Z180K30CatalogueAlternativeV65 (V : RawSet) where
  validSixSet : validSixSetB V = true
  o : Fin 8
  affineOrbit :
    affineEquivalentB V (z180K30ExceptionalOrbitColumnV4 o) = true
  starAlternative :
    o = 7 ∨
      ∃ U' : Fin 5 → RawSet,
        (∀ i, U' i ∈ z180K30ExceptionalOrbitChoicesV4 o) ∧
          Z180K30ExceptionalOrbitStarCoordinatesV4 o U'

theorem z180K30CatalogueAlternativeV65_orbit_eq_seven
    {V : RawSet} (h : Z180K30CatalogueAlternativeV65 V) :
    h.o = 7 := by
  rcases h.starAlternative with ho | ⟨U', hmem, hstar⟩
  · exact ho
  · exact z180_k30_exceptional_star_coordinates_force_H_v5
      h.o U' hmem hstar

theorem z180_k30_catalogue_alternative_force_H_v65
    {V : RawSet} (h : Z180K30CatalogueAlternativeV65 V) :
    validSixSetB V = true ∧
      affineEquivalentB V z180K30ExceptionalH = true := by
  refine ⟨h.validSixSet, ?_⟩
  have ho := z180K30CatalogueAlternativeV65_orbit_eq_seven h
  simpa [ho, z180K30ExceptionalOrbitColumnV4,
    z180K30ExceptionalH] using h.affineOrbit

#print axioms z180_k30_catalogue_alternative_force_H_v65

end Fuglede.Z180K30ExceptionalRawV2
