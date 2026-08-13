import Fuglede.Z180K30NormalCommonSpectrumV58
import Fuglede.Z180K30ExceptionalHCaseV3

namespace Fuglede

noncomputable section

noncomputable def z180K30ExceptionalBoundaryOfGramV60
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (ProjectiveAlternative ResidueCandidate : Fin 5 → Prop)
    (rankTwoProjective : ∀ s,
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue →
        ProjectiveAlternative s)
    (fourierProjectiveClasses : ∀ s,
      ProjectiveAlternative s → ResidueCandidate s) :
    Z180K30ExceptionalExternalBoundary A L where
  ExceptionalColumn := fun s =>
    Z180K30ExceptionalGramEigenvalueData
      (z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue
  ProjectiveAlternative := ProjectiveAlternative
  ResidueCandidate := ResidueCandidate
  columnDichotomy := z180_k30_column_dichotomy_v58 hSpec hcard data
  rankTwoProjective := rankTwoProjective
  fourierProjectiveClasses := fourierProjectiveClasses

theorem z180_k30_common_spectrum_or_projection30_injOn_of_gram_bridges_v60
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (ProjectiveAlternative ResidueCandidate : Fin 5 → Prop)
    (rankTwoProjective : ∀ s,
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue →
        ProjectiveAlternative s)
    (fourierProjectiveClasses : ∀ s,
      ProjectiveAlternative s → ResidueCandidate s)
    (certifiedOnlyH : ∀ s, ResidueCandidate s →
      Z180K30HCosetColumnConcrete L s) :
    (∃ s, Z180K30CommonSpectrumAt A L s) ∨
      Set.InjOn z180K30Projection30 (A : Set (ZMod 180)) := by
  let boundary := z180K30ExceptionalBoundaryOfGramV60
    hSpec hcard data ProjectiveAlternative ResidueCandidate
      rankTwoProjective fourierProjectiveClasses
  let certificate : Z180K30ExactExceptionalCertificate boundary :=
    z180K30ExactExceptionalCertificateOfConcreteH certifiedOnlyH
  let hHCase : Z180K30ExceptionalHCaseBridge certificate :=
    z180K30ExceptionalHCaseBridgeOfConcrete
      certificate hSpec hcard (fun _ h => h)
  exact z180_k30_common_spectrum_or_projection30_injOn_of_boundary
    boundary certificate hHCase

#print axioms z180_k30_common_spectrum_or_projection30_injOn_of_gram_bridges_v60

end
end Fuglede
