import Fuglede.Z180K30OriginalFourierBlockDefsV25
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-! Entrywise Gram formula for the actual blocks of the global matrix. -/

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

noncomputable def z180K30FifthSliceFourierSumV26
    (X : Finset (ZMod 180)) (r : Fin 5) (d : ZMod 180) : Complex :=
  ∑ x ∈ z180K30FifthSlice X (r.val : ZMod 5),
    ZMod.stdAddChar (x * d)

theorem z180K30OriginalFourierBlockV25_conjTranspose_mul_apply
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (j k : Fin 6) :
    (Matrix.conjTranspose (z180K30OriginalFourierBlockV25 data r s) *
        z180K30OriginalFourierBlockV25 data r s) j k =
      z180K30FifthSliceFourierSumV26 A r
        (z180K30OriginalFibreEnumV25 L s (data.cardL s) k -
          z180K30OriginalFibreEnumV25 L s (data.cardL s) j) := by
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV25 L s (data.cardL s) k -
      z180K30OriginalFibreEnumV25 L s (data.cardL s) j
  have hterm (a : Fin 6) :
      star (z180K30OriginalFourierBlockV25 data r s a j) *
          z180K30OriginalFourierBlockV25 data r s a k =
        ZMod.stdAddChar
          (z180K30OriginalFibreEnumV25 A r (data.cardA r) a * d) := by
    rw [z180K30OriginalFourierBlockV25_apply,
      z180K30OriginalFourierBlockV25_apply, star_stdAddChar,
      ← AddChar.map_add_eq_mul]
    congr 1
    dsimp only [d]
    ring
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  simp_rw [hterm]
  unfold z180K30FifthSliceFourierSumV26
  rw [← Finset.sum_attach]
  simpa only [z180K30OriginalFibreEnumV25] using
    (Equiv.sum_comp
      ((Finset.equivFinOfCardEq
        (z180K30FifthSlice_card_of_projected_card A r
          (data.cardA r))).symm)
      (fun a : ↑(z180K30FifthSlice A (r.val : ZMod 5)) =>
        ZMod.stdAddChar (a.1 * d)))

#print axioms z180K30OriginalFourierBlockV25_conjTranspose_mul_apply

end
end Fuglede
