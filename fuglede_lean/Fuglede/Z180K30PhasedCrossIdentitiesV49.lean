import Fuglede.Z180K30FifthSliceFactorizationV47
import Fuglede.Z180K30OriginalFourierBlockCrossEntriesV48
import Fuglede.Z180K30OriginalFourierBlockSumV35
import Mathlib.Tactic

namespace Fuglede

open scoped ComplexConjugate

noncomputable section

theorem z180K30FifthSlice_phase_normalized_eq_v49
    (X : Finset (ZMod 180)) (d : ZMod 180)
    (hfifth : crt180FifthCoord (toCRT180 d) ≠ 0)
    (hzero : CyclotomicZero 180 X d) (r u : Fin 5) :
    star (ZMod.stdAddChar
        (crt180FifthCoord (toCRT180 d) * (r.val : ZMod 5))) *
        z180K30FifthSliceFourierSumV34 X r d =
      star (ZMod.stdAddChar
        (crt180FifthCoord (toCRT180 d) * (u.val : ZMod 5))) *
        z180K30FifthSliceFourierSumV34 X u d := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomicZero_eraseV45
    X d hfifth hzero
  have hcancel (q : ZMod 5) :
      star (ZMod.stdAddChar q) * ZMod.stdAddChar q = 1 := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    simp
  calc
    star (ZMod.stdAddChar
        (crt180FifthCoord (toCRT180 d) * (r.val : ZMod 5))) *
        z180K30FifthSliceFourierSumV34 X r d =
      (star (ZMod.stdAddChar
          (crt180FifthCoord (toCRT180 d) * (r.val : ZMod 5))) *
        ZMod.stdAddChar
          (crt180FifthCoord (toCRT180 d) * (r.val : ZMod 5))) *
        z180FiveLevelFourierSum X
          (z180K30EraseFifthCoordinateV45 d) (r.val : ZMod 5)) := by
      rw [z180K30FifthSliceFourierSumV34_eq_phase_mul_fiveLevelV47,
        ← mul_assoc]
    _ = z180FiveLevelFourierSum X
        (z180K30EraseFifthCoordinateV45 d) (r.val : ZMod 5) := by
      rw [hcancel, one_mul]
    _ = z180FiveLevelFourierSum X
        (z180K30EraseFifthCoordinateV45 d) (u.val : ZMod 5) :=
      heq _ _
    _ = star (ZMod.stdAddChar
        (crt180FifthCoord (toCRT180 d) * (u.val : ZMod 5))) *
        z180K30FifthSliceFourierSumV34 X u d := by
      rw [z180K30FifthSliceFourierSumV34_eq_phase_mul_fiveLevelV47,
        ← mul_assoc, hcancel, one_mul]

theorem z180K30L_difference_fifthCoord_v49
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (s t : Fin 5) (j k : Fin 6) :
    crt180FifthCoord (toCRT180
      (z180K30OriginalFibreEnumV32 L t (data.cardL t) k -
        z180K30OriginalFibreEnumV32 L s (data.cardL s) j)) =
      (t.val : ZMod 5) - (s.val : ZMod 5) := by
  rw [crt180FifthCoord_toCRT180,
    ZMod.cast_sub (by norm_num : 5 ∣ 180),
    z180K30OriginalFibreEnumV32_fifth,
    z180K30OriginalFibreEnumV32_fifth]

theorem z180K30A_difference_fifthCoord_v49
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u : Fin 5) (i k : Fin 6) :
    crt180FifthCoord (toCRT180
      (z180K30OriginalFibreEnumV32 A r (data.cardA r) i -
        z180K30OriginalFibreEnumV32 A u (data.cardA u) k)) =
      (r.val : ZMod 5) - (u.val : ZMod 5) := by
  rw [crt180FifthCoord_toCRT180,
    ZMod.cast_sub (by norm_num : 5 ∣ 180),
    z180K30OriginalFibreEnumV32_fifth,
    z180K30OriginalFibreEnumV32_fifth]

theorem z180K30OriginalFourierBlockV32_phased_column_cross_v49
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s t : Fin 5) (hst : s ≠ t) :
    star (ZMod.stdAddChar
        (((t.val : ZMod 5) - (s.val : ZMod 5)) * (r.val : ZMod 5))) •
        (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
          z180K30OriginalFourierBlockV32 data r t) =
      star (ZMod.stdAddChar
        (((t.val : ZMod 5) - (s.val : ZMod 5)) * (u.val : ZMod 5))) •
        (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data u s) *
          z180K30OriginalFourierBlockV32 data u t) := by
  ext j k
  simp only [Matrix.smul_apply,
    z180K30OriginalFourierBlockV32_conjTranspose_mul_cross_apply_v48]
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 L t (data.cardL t) k -
      z180K30OriginalFibreEnumV32 L s (data.cardL s) j
  have hcoord : crt180FifthCoord (toCRT180 d) =
      (t.val : ZMod 5) - (s.val : ZMod 5) := by
    exact z180K30L_difference_fifthCoord_v49 data s t j k
  have hfifth : crt180FifthCoord (toCRT180 d) ≠ 0 := by
    rw [hcoord]
    intro hz
    have htsZ : (t.val : ZMod 5) = (s.val : ZMod 5) := sub_eq_zero.mp hz
    have hts : t = s := z180K30FinFiveEquivZModFiveV35.injective htsZ
    exact hst hts.symm
  have hmemt : z180K30OriginalFibreEnumV32 L t (data.cardL t) k ∈ L :=
    z180K30OriginalFibreEnumV32_mem L t (data.cardL t) k
  have hmems : z180K30OriginalFibreEnumV32 L s (data.cardL s) j ∈ L :=
    z180K30OriginalFibreEnumV32_mem L s (data.cardL s) j
  have hne : z180K30OriginalFibreEnumV32 L t (data.cardL t) k ≠
      z180K30OriginalFibreEnumV32 L s (data.cardL s) j := by
    intro heq
    have hc := congrArg (fun x : ZMod 180 => (ZMod.cast x : ZMod 5)) heq
    rw [z180K30OriginalFibreEnumV32_fifth,
      z180K30OriginalFibreEnumV32_fifth] at hc
    have hts : t = s := z180K30FinFiveEquivZModFiveV35.injective hc
    exact hst hts.symm
  have hzero : CyclotomicZero 180 A d :=
    hSpec.2.2 _ hmemt _ hmems hne
  have hphase := z180K30FifthSlice_phase_normalized_eq_v49
    A d hfifth hzero r u
  simpa only [d, hcoord] using hphase

theorem z180K30OriginalFourierBlockV32_phased_row_cross_v49
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (r u s t : Fin 5) (hru : r ≠ u) :
    star (ZMod.stdAddChar
        (((r.val : ZMod 5) - (u.val : ZMod 5)) * (s.val : ZMod 5))) •
        (z180K30OriginalFourierBlockV32 data r s *
          Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data u s)) =
      star (ZMod.stdAddChar
        (((r.val : ZMod 5) - (u.val : ZMod 5)) * (t.val : ZMod 5))) •
        (z180K30OriginalFourierBlockV32 data r t *
          Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data u t)) := by
  ext i k
  simp only [Matrix.smul_apply,
    z180K30OriginalFourierBlockV32_mul_conjTranspose_cross_apply_v48]
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 A r (data.cardA r) i -
      z180K30OriginalFibreEnumV32 A u (data.cardA u) k
  have hcoord : crt180FifthCoord (toCRT180 d) =
      (r.val : ZMod 5) - (u.val : ZMod 5) := by
    exact z180K30A_difference_fifthCoord_v49 data r u i k
  have hfifth : crt180FifthCoord (toCRT180 d) ≠ 0 := by
    rw [hcoord]
    intro hz
    have hruZ : (r.val : ZMod 5) = (u.val : ZMod 5) := sub_eq_zero.mp hz
    exact hru (z180K30FinFiveEquivZModFiveV35.injective hruZ)
  have hmemr : z180K30OriginalFibreEnumV32 A r (data.cardA r) i ∈ A :=
    z180K30OriginalFibreEnumV32_mem A r (data.cardA r) i
  have hmemu : z180K30OriginalFibreEnumV32 A u (data.cardA u) k ∈ A :=
    z180K30OriginalFibreEnumV32_mem A u (data.cardA u) k
  have hne : z180K30OriginalFibreEnumV32 A r (data.cardA r) i ≠
      z180K30OriginalFibreEnumV32 A u (data.cardA u) k := by
    intro heq
    have hc := congrArg (fun x : ZMod 180 => (ZMod.cast x : ZMod 5)) heq
    rw [z180K30OriginalFibreEnumV32_fifth,
      z180K30OriginalFibreEnumV32_fifth] at hc
    exact hru (z180K30FinFiveEquivZModFiveV35.injective hc)
  have hdual := cyclotomicSpectrum_dual hSpec
  have hzero : CyclotomicZero 180 L d :=
    hdual.2.2 _ hmemr _ hmemu hne
  have hphase := z180K30FifthSlice_phase_normalized_eq_v49
    L d hfifth hzero s t
  simpa only [d, hcoord] using hphase

#print axioms z180K30FifthSlice_phase_normalized_eq_v49
#print axioms z180K30OriginalFourierBlockV32_phased_column_cross_v49
#print axioms z180K30OriginalFourierBlockV32_phased_row_cross_v49

end
end Fuglede
