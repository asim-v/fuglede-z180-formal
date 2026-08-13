import Fuglede.Z180K30ExceptionalTilingClosureV61
import Fuglede.Z180K30RawHCosetConcreteV66Fix

/-!
# K30 tiling closure from the exact exceptional catalogue bridge

All analytic normal-branch and H-coset tiling arguments are already sealed.
This wrapper isolates the remaining statement to one precise bridge: an
exceptional real Gram column must produce the finite catalogue alternative
for its faithful raw fibre.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

theorem z180_k30_exists_tiling_of_catalogue_bridge_v68Fix
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (hcatalogue : ∀ s : Fin 5,
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue →
      Z180K30CatalogueAlternativeV65
        (z180K30RawFibreV63Fix L s (data.cardL s))) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k30_exists_tiling_of_gram_bridges_v61
    hSpec hcard data
      (fun s => Nonempty
        (Z180K30CatalogueAlternativeV65
          (z180K30RawFibreV63Fix L s (data.cardL s))))
      (fun s => Nonempty
        (Z180K30CatalogueAlternativeV65
          (z180K30RawFibreV63Fix L s (data.cardL s))))
  · intro s hs
    exact ⟨hcatalogue s hs⟩
  · intro _ hs
    exact hs
  · intro s hs
    rcases hs with ⟨hcat⟩
    exact z180_k30_HCosetColumnConcrete_of_catalogue_v66Fix
      L s (data.cardL s) hcat

#print axioms z180_k30_exists_tiling_of_catalogue_bridge_v68Fix

end
end Fuglede
