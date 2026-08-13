import Fuglede.Z180K30OriginalFourierBlockDefsV32
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-! Entrywise Gram formula for the actual blocks of the global matrix. -/

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

noncomputable def z180K30FifthSliceFourierSumV34
    (X : Finset (ZMod 180)) (r : Fin 5) (d : ZMod 180) : Complex :=
  ∑ x ∈ z180K30FifthSlice X (r.val : ZMod 5),
    ZMod.stdAddChar (x * d)

theorem z180K30OriginalFourierBlockV32_conjTranspose_mul_apply_v34
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (j k : Fin 6) :
    (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r s) j k =
      z180K30FifthSliceFourierSumV34 A r
        (z180K30OriginalFibreEnumV32 L s (data.cardL s) k -
          z180K30OriginalFibreEnumV32 L s (data.cardL s) j) := by
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 L s (data.cardL s) k -
      z180K30OriginalFibreEnumV32 L s (data.cardL s) j
  have hterm (a : Fin 6) :
      star (z180K30OriginalFourierBlockV32 data r s a j) *
          z180K30OriginalFourierBlockV32 data r s a k =
        ZMod.stdAddChar
          (z180K30OriginalFibreEnumV32 A r (data.cardA r) a * d) := by
    rw [z180K30OriginalFourierBlockV32_apply,
      z180K30OriginalFourierBlockV32_apply, star_stdAddChar,
      ← AddChar.map_add_eq_mul]
    congr 1
    dsimp only [d]
    ring
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  simp_rw [hterm]
  unfold z180K30FifthSliceFourierSumV34
  calc
    (∑ a : Fin 6,
      ZMod.stdAddChar
        (z180K30OriginalFibreEnumV32 A r (data.cardA r) a * d)) =
        ∑ a : ↑(z180K30FifthSlice A (r.val : ZMod 5)),
          ZMod.stdAddChar (a.1 * d) := by
      simpa only [z180K30OriginalFibreEnumV32] using
        (Equiv.sum_comp
          ((Finset.equivFinOfCardEq
            (z180K30FifthSlice_card_of_projected_card_v31 A r
              (data.cardA r))).symm)
          (fun a : ↑(z180K30FifthSlice A (r.val : ZMod 5)) =>
            ZMod.stdAddChar (a.1 * d)))
    _ = ∑ x ∈ z180K30FifthSlice A (r.val : ZMod 5),
        ZMod.stdAddChar (x * d) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (z180K30FifthSlice A (r.val : ZMod 5))
          (fun x => ZMod.stdAddChar (x * d)))

#print axioms z180K30OriginalFourierBlockV32_conjTranspose_mul_apply_v34

end
end Fuglede
