import Fuglede.Z180K30FourierBlockDefsV22

/-! Cardinality of the original fifth slice from its projected fibre. -/

namespace Fuglede

theorem z180K30FifthSlice_card_of_projected_card_v31
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
  calc
    (z180K30FifthSlice X (i.val : ZMod 5)).card =
        ((z180K30FifthSlice X (i.val : ZMod 5)).image
          (fun x => (ZMod.cast x : ZMod 36))).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (z180K30FifthFibres36 X i).card := by
      rfl
    _ = 6 := hcard

#print axioms z180K30FifthSlice_card_of_projected_card_v31

end Fuglede
