import Fuglede.Z180K30FourierBlockDefsV22
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-! Entrywise Gram formula for the concrete six-by-six Fourier blocks. -/

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

theorem z180K30FourierBlockV22_conjTranspose_mul_apply
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (j k : Fin 6) :
    (Matrix.conjTranspose (z180K30FourierBlockV22 data r s) *
        z180K30FourierBlockV22 data r s) j k =
      fourierSum (z180K30FifthFibres36 A r)
        (z180K30FibreEnumV22 L s (data.cardL s) k -
          z180K30FibreEnumV22 L s (data.cardL s) j) := by
  let d : ZMod 36 :=
    z180K30FibreEnumV22 L s (data.cardL s) k -
      z180K30FibreEnumV22 L s (data.cardL s) j
  have hterm (a : Fin 6) :
      star (z180K30FourierBlockV22 data r s a j) *
          z180K30FourierBlockV22 data r s a k =
        ZMod.stdAddChar
          (z180K30FibreEnumV22 A r (data.cardA r) a * d) := by
    rw [z180K30FourierBlockV22_apply,
      z180K30FourierBlockV22_apply, star_stdAddChar,
      ← AddChar.map_add_eq_mul]
    congr 1
    dsimp only [d]
    ring
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  simp_rw [hterm]
  rw [fourierSum]
  simpa only [z180K30FibreEnumV22] using
    (Equiv.sum_comp
      ((Finset.equivFinOfCardEq (data.cardA r)).symm)
      (fun a : ↑(z180K30FifthFibres36 A r) =>
        ZMod.stdAddChar (a.1 * d)))

#print axioms z180K30FourierBlockV22_conjTranspose_mul_apply

end
end Fuglede
