import Fuglede.Z180K30FourierBlockDefsV22
import Mathlib.Data.Fintype.EquivFin

/-!
The actual `6 x 6` blocks cut out of the global Fourier matrix.  Unlike the
projected-coordinate pilot, these entries use representatives in `ZMod 180`
itself, so all spectral orthogonality identities apply without a hidden CRT
unit factor.
-/

namespace Fuglede

noncomputable section

theorem z180K30FifthSlice_card_of_projected_card
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    (z180K30FifthSlice X (i.val : ZMod 5)).card = 6 := by
  have hinj : Set.InjOn
      (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (z180K30FifthSlice X (i.val : ZMod 5) : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply z180_k30_cast36_injective_on_fifth_fibre
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy
  simpa only [z180K30FifthFibres36, z180K30Fibre,
      z180K30FifthSlice, Finset.card_image_iff.mpr hinj] using hcard

noncomputable def z180K30OriginalFibreEnumV25
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Fin 6 → ZMod 180 :=
  fun k =>
    ((Finset.equivFinOfCardEq
      (z180K30FifthSlice_card_of_projected_card X i hcard)).symm k).1

theorem z180K30OriginalFibreEnumV25_mem_slice
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30OriginalFibreEnumV25 X i hcard k ∈
      z180K30FifthSlice X (i.val : ZMod 5) :=
  ((Finset.equivFinOfCardEq
    (z180K30FifthSlice_card_of_projected_card X i hcard)).symm k).2

theorem z180K30OriginalFibreEnumV25_mem
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30OriginalFibreEnumV25 X i hcard k ∈ X := by
  exact (Finset.mem_filter.mp
    (z180K30OriginalFibreEnumV25_mem_slice X i hcard k)).1

theorem z180K30OriginalFibreEnumV25_fifth
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    (ZMod.cast (z180K30OriginalFibreEnumV25 X i hcard k) : ZMod 5) =
      (i.val : ZMod 5) := by
  exact (Finset.mem_filter.mp
    (z180K30OriginalFibreEnumV25_mem_slice X i hcard k)).2

theorem z180K30OriginalFibreEnumV25_injective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Function.Injective (z180K30OriginalFibreEnumV25 X i hcard) := by
  intro k l hkl
  apply (Finset.equivFinOfCardEq
    (z180K30FifthSlice_card_of_projected_card X i hcard)).symm.injective
  exact Subtype.ext hkl

noncomputable def z180K30OriginalFourierBlockV25
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) : Z180K30BlockMatrixV19 :=
  Matrix.of fun a l => ZMod.stdAddChar
    (z180K30OriginalFibreEnumV25 A r (data.cardA r) a *
      z180K30OriginalFibreEnumV25 L s (data.cardL s) l)

@[simp]
theorem z180K30OriginalFourierBlockV25_apply
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30OriginalFourierBlockV25 data r s a l = ZMod.stdAddChar
      (z180K30OriginalFibreEnumV25 A r (data.cardA r) a *
        z180K30OriginalFibreEnumV25 L s (data.cardL s) l) := rfl

theorem z180K30OriginalFourierBlockV25_entry_ne_zero
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30OriginalFourierBlockV25 data r s a l ≠ 0 := by
  rw [z180K30OriginalFourierBlockV25_apply, ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

#print axioms z180K30FifthSlice_card_of_projected_card
#print axioms z180K30OriginalFibreEnumV25_injective
#print axioms z180K30OriginalFourierBlockV25_entry_ne_zero

end
end Fuglede
