import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# A one-point Fourier support lemma on `ZMod`

The finite Fourier transform of a function on `ZMod N` is supported at zero
exactly when the function is constant.  We only need the forward implication:
vanishing at every nonzero frequency forces equality of all fibres.

This is the abstract Fourier-inversion step behind the five-fibre descent used
for `ZMod 180`.
-/

namespace Fuglede

open scoped BigOperators ZMod

variable {N : Nat} [NeZero N]

/-- If the DFT of a complex-valued function on `ZMod N` vanishes away from
zero, then the function is constant. -/
theorem eq_of_dft_eq_zero_off_zero
    (S : ZMod N → ℂ)
    (hzero : ∀ b : ZMod N, b ≠ 0 → ZMod.dft S b = 0) :
    ∀ c c' : ZMod N, S c = S c' := by
  intro c c'
  have hsum (x : ZMod N) :
      ZMod.dft (ZMod.dft S) x = ZMod.dft S 0 := by
    rw [ZMod.dft_apply]
    classical
    calc
      (∑ b : ZMod N, ZMod.stdAddChar (-(b * x)) • ZMod.dft S b) =
          ZMod.stdAddChar (-(0 * x)) • ZMod.dft S 0 := by
            apply Finset.sum_eq_single 0
            · intro b _ hb
              rw [hzero b hb]
              exact smul_zero _
            · simp
      _ = ZMod.dft S 0 := by simp
  have hc := congrFun (ZMod.dft_dft S) (-c)
  have hc' := congrFun (ZMod.dft_dft S) (-c')
  rw [hsum, neg_neg] at hc hc'
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  rw [smul_eq_mul] at hc hc'
  exact mul_left_cancel₀ hN (hc.symm.trans hc')

end Fuglede
