import Fuglede.Z180K30OriginalFibreCardV31
import Mathlib.Data.Fintype.EquivFin

/-! Actual `6 x 6` blocks cut out of the global Fourier matrix. -/

namespace Fuglede

noncomputable section

noncomputable def z180K30OriginalFibreEnumV32
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Fin 6 → ZMod 180 :=
  fun k =>
    ((Finset.equivFinOfCardEq
      (z180K30FifthSlice_card_of_projected_card_v31 X i hcard)).symm k).1

theorem z180K30OriginalFibreEnumV32_mem_slice
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30OriginalFibreEnumV32 X i hcard k ∈
      z180K30FifthSlice X (i.val : ZMod 5) :=
  ((Finset.equivFinOfCardEq
    (z180K30FifthSlice_card_of_projected_card_v31 X i hcard)).symm k).2

theorem z180K30OriginalFibreEnumV32_mem
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30OriginalFibreEnumV32 X i hcard k ∈ X := by
  exact (Finset.mem_filter.mp
    (z180K30OriginalFibreEnumV32_mem_slice X i hcard k)).1

theorem z180K30OriginalFibreEnumV32_fifth
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    (ZMod.cast (z180K30OriginalFibreEnumV32 X i hcard k) : ZMod 5) =
      (i.val : ZMod 5) := by
  exact (Finset.mem_filter.mp
    (z180K30OriginalFibreEnumV32_mem_slice X i hcard k)).2

theorem z180K30OriginalFibreEnumV32_injective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Function.Injective (z180K30OriginalFibreEnumV32 X i hcard) := by
  intro k l hkl
  apply (Finset.equivFinOfCardEq
    (z180K30FifthSlice_card_of_projected_card_v31 X i hcard)).symm.injective
  exact Subtype.ext hkl

noncomputable def z180K30OriginalFourierBlockV32
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) : Z180K30BlockMatrixV19 :=
  Matrix.of fun a l => ZMod.stdAddChar
    (z180K30OriginalFibreEnumV32 A r (data.cardA r) a *
      z180K30OriginalFibreEnumV32 L s (data.cardL s) l)

@[simp]
theorem z180K30OriginalFourierBlockV32_apply
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30OriginalFourierBlockV32 data r s a l = ZMod.stdAddChar
      (z180K30OriginalFibreEnumV32 A r (data.cardA r) a *
        z180K30OriginalFibreEnumV32 L s (data.cardL s) l) := rfl

theorem z180K30OriginalFourierBlockV32_entry_ne_zero
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30OriginalFourierBlockV32 data r s a l ≠ 0 := by
  rw [z180K30OriginalFourierBlockV32_apply, ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

#print axioms z180K30OriginalFibreEnumV32_injective
#print axioms z180K30OriginalFourierBlockV32_entry_ne_zero

end
end Fuglede
