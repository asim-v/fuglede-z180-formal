import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180K4TypedAdapter

/-!
# Unconditional closure of the cardinality-four branch in `ZMod 180`

The typed adapter rules out collisions modulo four using the sealed DPLL
certificate.  The CRT Ramanujan theorem discharges its only two transform
hypotheses.
-/

namespace Fuglede

/-- Every cardinality-four spectral set in `ZMod 180` is a complete
transversal modulo four. -/
theorem z180_k4_projection4_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 4) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 4))
      (A : Set (ZMod 180)) := by
  exact z180_k4_projection4_injOn_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- The explicit complement is the kernel of reduction modulo four. -/
theorem z180_k4_tiles_projection4_kernel_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 4) :
    Tiles A (kernelFinset
      (ZMod.castHom (by norm_num : 4 ∣ 180) (ZMod 4)).toAddMonoidHom) := by
  exact z180_k4_tiles_projection4_kernel_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- Unconditional existential tiling endpoint for cardinality four. -/
theorem z180_k4_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 4) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact z180_k4_exists_tiling_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

#print axioms z180_k4_projection4_injOn_of_spectral
#print axioms z180_k4_tiles_projection4_kernel_of_spectral
#print axioms z180_k4_exists_tiling_of_spectral

end Fuglede
