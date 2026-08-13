import Fuglede.Z180MasterReductionK33
import Fuglede.Z180K6UnconditionalClosure
import Fuglede.Z180K10Closure
import Fuglede.Z180K12UnconditionalClosure
import Fuglede.Z180K18UnconditionalClosure
import Fuglede.Z180NondivisorK24Closure

/-!
# Final master interface after the cardinality-eighteen closure

The sealed closures at cardinalities `6`, `10`, `12`, and `18` reduce the
master theorem to the two genuine remaining boundaries.  Cardinality `24`
is represented by its intended nondivisor exclusion, while cardinality `30`
is represented by a direct spectral-to-tiling closure.  Both are explicit
premises here; this module does not manufacture either endpoint.
-/

namespace Fuglede

/-- Exact interface expected from the cardinality-twenty-four exclusion. -/
def Z180K24SpectralExclusion : Prop :=
  ∀ {A L : Finset (ZMod 180)},
    CyclotomicSpectrum 180 A L → A.card ≠ 24

/-- Exact interface expected from the cardinality-thirty closure. -/
def Z180K30SpectralTilingClosure : Prop :=
  ∀ {A L : Finset (ZMod 180)},
    CyclotomicSpectrum 180 A L → A.card = 30 →
      ∃ B : Finset (ZMod 180), Tiles A B

/-- With the cardinality-eighteen endpoint sealed, only cardinalities
twenty-four and thirty remain in the master reduction. -/
theorem z180_spectral_master_reduction_to_twentyfour_thirty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      A.card = 24 ∨ A.card = 30 := by
  rcases z180_spectral_master_reduction_without_k33 hSpec with
    htiles | h6 | h10 | h12 | h18 | h30 | h24
  · exact Or.inl htiles
  · exact Or.inl (z180_k6_exists_tiling_of_spectral hSpec h6)
  · exact Or.inl (z180_k10_exists_tiling_of_spectral hSpec h10)
  · exact Or.inl (z180_k12_exists_tiling_of_spectral hSpec h12)
  · exact Or.inl (z180_k18_exists_tiling_of_spectral hSpec h18)
  · exact Or.inr (Or.inr h30)
  · exact Or.inr (Or.inl h24)

/-- Final spectral-to-tiling theorem, conditional exactly on the two open
cardinality interfaces and on nothing else. -/
theorem z180_exists_tiling_of_spectral_of_k24_exclusion_and_k30_closure
    (h24 : Z180K24SpectralExclusion)
    (h30 : Z180K30SpectralTilingClosure)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  rcases z180_spectral_master_reduction_to_twentyfour_thirty hSpec with
    htiles | hcard24 | hcard30
  · exact htiles
  · exact (h24 hSpec hcard24).elim
  · exact h30 hSpec hcard30

/-- After the sealed cardinality-twenty-four exclusion, the master reduction
has exactly one remaining branch: cardinality thirty. -/
theorem z180_spectral_master_reduction_to_thirty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨ A.card = 30 := by
  rcases z180_spectral_master_reduction_to_twentyfour_thirty hSpec with
    htiles | hcard24 | hcard30
  · exact Or.inl htiles
  · exact (z180_nondivisor_k24_card_ne_of_spectral hSpec hcard24).elim
  · exact Or.inr hcard30

/-- Final spectral-to-tiling theorem conditional only on the remaining
cardinality-thirty closure. -/
theorem z180_exists_tiling_of_spectral_of_k30_closure
    (h30 : Z180K30SpectralTilingClosure)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  rcases z180_spectral_master_reduction_to_thirty hSpec with htiles | hcard30
  · exact htiles
  · exact h30 hSpec hcard30

#print axioms z180_spectral_master_reduction_to_twentyfour_thirty
#print axioms z180_exists_tiling_of_spectral_of_k24_exclusion_and_k30_closure
#print axioms z180_spectral_master_reduction_to_thirty
#print axioms z180_exists_tiling_of_spectral_of_k30_closure

end Fuglede
