import Fuglede.Z180K30PhasedCrossIdentitiesV50
import Mathlib.Tactic

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

def z180K30DephasingPhaseV51 (r s : Fin 5) : Complex :=
  ZMod.stdAddChar ((r.val : ZMod 5) * (s.val : ZMod 5))

noncomputable def z180K30DephasedFourierBlockV51
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) : Z180K30BlockMatrixV19 :=
  star (z180K30DephasingPhaseV51 r s) •
    z180K30OriginalFourierBlockV32 data r s

theorem z180K30DephasingPhaseV51_column_ratio
    (r s t : Fin 5) :
    z180K30DephasingPhaseV51 r s *
        star (z180K30DephasingPhaseV51 r t) =
      star (ZMod.stdAddChar
        (((t.val : ZMod 5) - (s.val : ZMod 5)) *
          (r.val : ZMod 5))) := by
  unfold z180K30DephasingPhaseV51
  calc
    ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5)) *
        star (ZMod.stdAddChar
          ((r.val : ZMod 5) * (t.val : ZMod 5))) =
      ZMod.stdAddChar
        ((r.val : ZMod 5) * (s.val : ZMod 5) +
          -((r.val : ZMod 5) * (t.val : ZMod 5))) := by
        rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    _ = ZMod.stdAddChar
        (-(((t.val : ZMod 5) - (s.val : ZMod 5)) *
          (r.val : ZMod 5))) := by
        congr 1
        ring
    _ = star (ZMod.stdAddChar
        (((t.val : ZMod 5) - (s.val : ZMod 5)) *
          (r.val : ZMod 5))) := by
        rw [star_stdAddChar]

theorem z180K30DephasingPhaseV51_row_ratio
    (r u s : Fin 5) :
    star (z180K30DephasingPhaseV51 r s) *
        z180K30DephasingPhaseV51 u s =
      star (ZMod.stdAddChar
        (((r.val : ZMod 5) - (u.val : ZMod 5)) *
          (s.val : ZMod 5))) := by
  unfold z180K30DephasingPhaseV51
  calc
    star (ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5))) *
        ZMod.stdAddChar
          ((u.val : ZMod 5) * (s.val : ZMod 5)) =
      ZMod.stdAddChar
        (-((r.val : ZMod 5) * (s.val : ZMod 5)) +
          (u.val : ZMod 5) * (s.val : ZMod 5)) := by
        rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    _ = ZMod.stdAddChar
        (-(((r.val : ZMod 5) - (u.val : ZMod 5)) *
          (s.val : ZMod 5))) := by
        congr 1
        ring
    _ = star (ZMod.stdAddChar
        (((r.val : ZMod 5) - (u.val : ZMod 5)) *
          (s.val : ZMod 5))) := by
        rw [star_stdAddChar]

theorem z180K30DephasedFourierBlockV51_conjTranspose_mul
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s t : Fin 5) :
    Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r t =
      star (ZMod.stdAddChar
        (((t.val : ZMod 5) - (s.val : ZMod 5)) *
          (r.val : ZMod 5))) •
        (Matrix.conjTranspose
            (z180K30OriginalFourierBlockV32 data r s) *
          z180K30OriginalFourierBlockV32 data r t) := by
  unfold z180K30DephasedFourierBlockV51
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  simp only [star_star]
  rw [z180K30DephasingPhaseV51_column_ratio]

theorem z180K30DephasedFourierBlockV51_mul_conjTranspose
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s : Fin 5) :
    z180K30DephasedFourierBlockV51 data r s *
        Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u s) =
      star (ZMod.stdAddChar
        (((r.val : ZMod 5) - (u.val : ZMod 5)) *
          (s.val : ZMod 5))) •
        (z180K30OriginalFourierBlockV32 data r s *
          Matrix.conjTranspose
            (z180K30OriginalFourierBlockV32 data u s)) := by
  unfold z180K30DephasedFourierBlockV51
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  simp only [star_star]
  rw [z180K30DephasingPhaseV51_row_ratio]

theorem z180K30DephasedFourierBlockV51_column_cross
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s t : Fin 5) (hst : s ≠ t) :
    Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r t =
      Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u s) *
        z180K30DephasedFourierBlockV51 data u t := by
  rw [z180K30DephasedFourierBlockV51_conjTranspose_mul data r s t,
    z180K30DephasedFourierBlockV51_conjTranspose_mul data u s t]
  exact z180K30OriginalFourierBlockV32_phased_column_cross_v50
    hSpec data r u s t hst

theorem z180K30DephasedFourierBlockV51_row_cross
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s t : Fin 5) (hru : r ≠ u) :
    z180K30DephasedFourierBlockV51 data r s *
        Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u s) =
      z180K30DephasedFourierBlockV51 data r t *
        Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u t) := by
  rw [z180K30DephasedFourierBlockV51_mul_conjTranspose data r u s,
    z180K30DephasedFourierBlockV51_mul_conjTranspose data r u t]
  exact z180K30OriginalFourierBlockV32_phased_row_cross_v50
    hSpec data r u s t hru

@[simp]
theorem z180K30DephasedFourierBlockV51_gram_matrix
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) :
    Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r s =
      Matrix.conjTranspose
          (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r s := by
  simpa using
    (z180K30DephasedFourierBlockV51_conjTranspose_mul data r s s)

#print axioms z180K30DephasedFourierBlockV51_column_cross
#print axioms z180K30DephasedFourierBlockV51_row_cross
#print axioms z180K30DephasedFourierBlockV51_gram_matrix

end
end Fuglede
