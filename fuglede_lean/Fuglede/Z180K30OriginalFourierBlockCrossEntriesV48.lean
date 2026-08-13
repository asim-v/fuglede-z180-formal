import Fuglede.Z180K30OriginalFourierBlockGramV34
import Mathlib.Tactic

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

theorem z180K30OriginalFourierBlockV32_conjTranspose_mul_cross_apply_v48
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s t : Fin 5) (j k : Fin 6) :
    (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r t) j k =
      z180K30FifthSliceFourierSumV34 A r
        (z180K30OriginalFibreEnumV32 L t (data.cardL t) k -
          z180K30OriginalFibreEnumV32 L s (data.cardL s) j) := by
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 L t (data.cardL t) k -
      z180K30OriginalFibreEnumV32 L s (data.cardL s) j
  have hterm (a : Fin 6) :
      star (z180K30OriginalFourierBlockV32 data r s a j) *
          z180K30OriginalFourierBlockV32 data r t a k =
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

theorem z180K30OriginalFourierBlockV32_mul_conjTranspose_cross_apply_v48
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s : Fin 5) (i k : Fin 6) :
    (z180K30OriginalFourierBlockV32 data r s *
        Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data u s)) i k =
      z180K30FifthSliceFourierSumV34 L s
        (z180K30OriginalFibreEnumV32 A r (data.cardA r) i -
          z180K30OriginalFibreEnumV32 A u (data.cardA u) k) := by
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 A r (data.cardA r) i -
      z180K30OriginalFibreEnumV32 A u (data.cardA u) k
  have hterm (l : Fin 6) :
      z180K30OriginalFourierBlockV32 data r s i l *
          star (z180K30OriginalFourierBlockV32 data u s k l) =
        ZMod.stdAddChar
          (z180K30OriginalFibreEnumV32 L s (data.cardL s) l * d) := by
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
    (∑ l : Fin 6,
      ZMod.stdAddChar
        (z180K30OriginalFibreEnumV32 L s (data.cardL s) l * d)) =
        ∑ l : ↑(z180K30FifthSlice L (s.val : ZMod 5)),
          ZMod.stdAddChar (l.1 * d) := by
      simpa only [z180K30OriginalFibreEnumV32] using
        (Equiv.sum_comp
          ((Finset.equivFinOfCardEq
            (z180K30FifthSlice_card_of_projected_card_v31 L s
              (data.cardL s))).symm)
          (fun l : ↑(z180K30FifthSlice L (s.val : ZMod 5)) =>
            ZMod.stdAddChar (l.1 * d)))
    _ = ∑ x ∈ z180K30FifthSlice L (s.val : ZMod 5),
        ZMod.stdAddChar (x * d) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (z180K30FifthSlice L (s.val : ZMod 5))
          (fun x => ZMod.stdAddChar (x * d)))

#print axioms z180K30OriginalFourierBlockV32_conjTranspose_mul_cross_apply_v48
#print axioms z180K30OriginalFourierBlockV32_mul_conjTranspose_cross_apply_v48

end
end Fuglede
