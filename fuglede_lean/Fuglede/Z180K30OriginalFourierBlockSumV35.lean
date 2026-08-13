import Fuglede.Z180K30OriginalFourierBlockGramV34
import Fuglede.FourierTiling
import Mathlib.Tactic

/-! The five column-block Gram matrices sum to `30 I`. -/

namespace Fuglede

open scoped BigOperators

noncomputable section

def z180K30FinFiveEquivZModFiveV35 : Fin 5 ≃ ZMod 5 :=
  Equiv.ofBijective (fun i : Fin 5 => (i.val : ZMod 5)) (by decide)

@[simp]
theorem z180K30FinFiveEquivZModFiveV35_apply (i : Fin 5) :
    z180K30FinFiveEquivZModFiveV35 i = (i.val : ZMod 5) := rfl

theorem sum_z180K30FifthSliceFourierSumV34
    (X : Finset (ZMod 180)) (d : ZMod 180) :
    (∑ r : Fin 5, z180K30FifthSliceFourierSumV34 X r d) =
      fourierSum X d := by
  classical
  let weight : ZMod 180 → Complex := fun x => ZMod.stdAddChar (x * d)
  calc
    (∑ r : Fin 5, z180K30FifthSliceFourierSumV34 X r d) =
        ∑ c : ZMod 5, ∑ x ∈ X.filter
          (fun x => (ZMod.cast x : ZMod 5) = c), weight x := by
      simpa only [z180K30FifthSliceFourierSumV34,
        z180K30FifthSlice, weight,
        z180K30FinFiveEquivZModFiveV35_apply] using
        (Equiv.sum_comp z180K30FinFiveEquivZModFiveV35
          (fun c : ZMod 5 => ∑ x ∈ X.filter
            (fun x => (ZMod.cast x : ZMod 5) = c), weight x))
    _ = ∑ x ∈ X, weight x := by
      simpa only using Finset.sum_fiberwise X
        (fun x : ZMod 180 => (ZMod.cast x : ZMod 5)) weight
    _ = fourierSum X d := by
      exact (fourierSum_eq_finset_sum X d).symm

theorem z180K30OriginalFourierBlockV32_sum_gram_apply
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) (j k : Fin 6) :
    (∑ r : Fin 5,
      (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r s) j k) =
      if j = k then (30 : Complex) else 0 := by
  simp_rw [z180K30OriginalFourierBlockV32_conjTranspose_mul_apply_v34]
  rw [sum_z180K30FifthSliceFourierSumV34]
  by_cases hjk : j = k
  · subst k
    simp [fourierSum_zero, hcard]
  · rw [if_neg hjk]
    have hFourier :=
      (cyclotomicSpectrum_iff_fourierSpectrum A L).1 hSpec
    have hk : z180K30OriginalFibreEnumV32 L s (data.cardL s) k ∈ L :=
      z180K30OriginalFibreEnumV32_mem L s (data.cardL s) k
    have hj : z180K30OriginalFibreEnumV32 L s (data.cardL s) j ∈ L :=
      z180K30OriginalFibreEnumV32_mem L s (data.cardL s) j
    have hne :
        z180K30OriginalFibreEnumV32 L s (data.cardL s) k ≠
          z180K30OriginalFibreEnumV32 L s (data.cardL s) j := by
      intro heq
      have hkj := z180K30OriginalFibreEnumV32_injective
        L s (data.cardL s) heq
      exact hjk hkj.symm
    exact hFourier.2.2 _ hk _ hj hne

#print axioms sum_z180K30FifthSliceFourierSumV34
#print axioms z180K30OriginalFourierBlockV32_sum_gram_apply

end
end Fuglede
