import Fuglede.Z180K30ExceptionalHCaseV3
import Fuglede.Z180K30FibreTiling
import Fuglede.ProjectionTiling

/-!
# Conditional assembly of the K30 normal and exceptional branches

The statement remains explicitly conditional on the analytic boundary, the
exact finite certificate, and the honest interpretation of its surviving
orbit.  No inhabitant of those interfaces is asserted here.
-/

namespace Fuglede

theorem z180_k30_exists_tiling_of_exceptional_boundary
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (boundary : Z180K30ExceptionalExternalBoundary A L)
    (certificate : Z180K30ExactExceptionalCertificate boundary)
    (hhonest : ∀ s, certificate.HCosetColumn s →
      Z180K30HCosetColumnConcrete L s) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hHCase : Z180K30ExceptionalHCaseBridge certificate :=
    z180K30ExceptionalHCaseBridgeOfConcrete certificate hSpec hcard hhonest
  rcases z180_k30_common_spectrum_or_projection30_injOn_of_boundary
      boundary certificate hHCase with hcommon | hinj30
  · obtain ⟨s, hs⟩ := hcommon
    have hcardA := z180_k30_fibre_card_six hSpec hcard
    obtain ⟨B, hB⟩ :=
      z180_k30_five_fibres_common_complement_of_common_spectrum
        (z180K30FifthFibres36 A) (z180K30FifthFibres36 L s)
        (fun i ↦ hcardA (i.val : ZMod 5)) hs
    refine ⟨z180K30LiftComplement B,
      z180_k30_tiles_of_common_fibre_complement A B ?_⟩
    intro c
    have hc := hB (z180K30FinOfZMod5 c)
    simpa only [z180K30FifthFibres36, z180K30FinOfZMod5_cast] using hc
  · refine ⟨kernelFinset z180K30Projection30,
      transversal_tiles_kernel z180K30Projection30 A ?_ ?_⟩
    · exact (kernel_difference_free_iff_injOn z180K30Projection30 A).2 hinj30
    · simpa using hcard

#print axioms z180_k30_exists_tiling_of_exceptional_boundary

end Fuglede
