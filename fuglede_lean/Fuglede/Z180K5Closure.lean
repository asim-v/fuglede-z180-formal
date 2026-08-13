import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180K5TypedAdapter

/-!
# Unconditional closure of the cardinality-five branch in `ZMod 180`

The typed adapter reduces a hypothetical collision modulo five to the sealed
rational DPLL contradiction.  `CRT180RamanujanClosure` supplies the two
Ramanujan identities, leaving no additional hypothesis.
-/

namespace Fuglede

/-- Every cardinality-five spectral set in `ZMod 180` is a complete
transversal modulo five. -/
theorem z180_k5_projection5_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 5) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 5))
      (A : Set (ZMod 180)) := by
  exact z180_k5_projection5_injOn_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- The explicit complement is the kernel of reduction modulo five. -/
theorem z180_k5_tiles_projection5_kernel_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 5) :
    Tiles A (kernelFinset
      (ZMod.castHom (by norm_num : 5 ∣ 180) (ZMod 5)).toAddMonoidHom) := by
  exact z180_k5_tiles_projection5_kernel_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- Unconditional existential tiling endpoint for the cardinality-five
branch. -/
theorem z180_k5_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 5) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact z180_k5_exists_tiling_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

#print axioms z180_k5_projection5_injOn_of_spectral
#print axioms z180_k5_tiles_projection5_kernel_of_spectral
#print axioms z180_k5_exists_tiling_of_spectral

end Fuglede
