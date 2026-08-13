import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180K9TypedAdapter

/-!
# Unconditional closure of the cardinality-nine branch in `ZMod 180`

The typed adapter previously isolated the Ramanujan identity as its only
analytic hypothesis.  `CRT180RamanujanClosure` now proves that identity for
every finite set, so the projection and tiling endpoints are unconditional.
-/

namespace Fuglede

/-- Every cardinality-nine spectral set in `ZMod 180` is a complete
transversal modulo nine. -/
theorem z180_k9_projection9_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 9) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 9))
      (A : Set (ZMod 180)) := by
  exact z180_k9_projection9_injOn_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- The explicit complement is the kernel of reduction modulo nine. -/
theorem z180_k9_tiles_projection9_kernel_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 9) :
    Tiles A (kernelFinset
      (ZMod.castHom (by norm_num : 9 ∣ 180) (ZMod 9)).toAddMonoidHom) := by
  exact z180_k9_tiles_projection9_kernel_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- Existential tiling endpoint for the cardinality-nine branch. -/
theorem z180_k9_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 9) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact z180_k9_exists_tiling_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

end Fuglede
