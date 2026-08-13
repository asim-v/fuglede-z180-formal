import Fuglede.Z180K12M6Order20Phi6Difference
import Fuglede.Z180K12Projection36Remainders18
import Fuglede.Z180K6LowOrderPhi23Compact
import Mathlib.Tactic

/-!
# Alternating modulo-nine fibres from `Phi_2`, `Phi_6`, and `Phi_18`

For a function on `ZMod 36`, its alternating sum on the four points above a
fixed residue modulo nine is the Fourier transform in the order-two
coordinate.  The exact orders `2`, `6`, and `18` cover all nine frequencies
of the remaining `ZMod 9` coordinate.  The theorem below proves the resulting
inversion entirely over `Int`, using the already sealed explicit
cyclotomic-remainder identities.

This is the table-free arithmetic core of the high-order pair geometry in the
cardinality-eighteen, `m = 12` branch.  It has no cardinality or set-level
hypotheses.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Alternating sum on the four projected coordinates above `r : ZMod 9`.
The signs are the ordinary parity signs of the representatives in
`{r,r+9,r+18,r+27}`. -/
def z180K18M12SignedNineFiber
    (b : Fin 36 → Int) (r : ZMod 9) : Int :=
  match r.val with
  | 0 => b 0 - b 9 + b 18 - b 27
  | 1 => -b 1 + b 10 - b 19 + b 28
  | 2 => b 2 - b 11 + b 20 - b 29
  | 3 => -b 3 + b 12 - b 21 + b 30
  | 4 => b 4 - b 13 + b 22 - b 31
  | 5 => -b 5 + b 14 - b 23 + b 32
  | 6 => b 6 - b 15 + b 24 - b 33
  | 7 => -b 7 + b 16 - b 25 + b 34
  | _ => b 8 - b 17 + b 26 - b 35

/-- Divisibility by `Phi_2` is exactly the vanishing of the total parity
balance of the thirty-six coefficients. -/
theorem projection36_phi2_parity_balance
    (b : Fin 36 → Int)
    (htwo : cyclotomic 2 Int ∣ projection36IndicatorMask b) :
    b 0 - b 1 + b 2 - b 3 + b 4 - b 5 +
      b 6 - b 7 + b 8 - b 9 + b 10 - b 11 +
      b 12 - b 13 + b 14 - b 15 + b 16 - b 17 +
      b 18 - b 19 + b 20 - b 21 + b 22 - b 23 +
      b 24 - b 25 + b 26 - b 27 + b 28 - b 29 +
      b 30 - b 31 + b 32 - b 33 + b 34 - b 35 = 0 := by
  have hdiff :=
    cyclotomic_dvd_projection36Indicator_sub_residue6 b 2 (by norm_num)
  have hresidue : cyclotomic 2 Int ∣ projection36ResidueMask6 b := by
    have hsub := dvd_sub htwo hdiff
    simpa using hsub
  rw [projection36ResidueMask6_eq_k6ResiduePolynomial6] at hresidue
  have hroot : eval (-1 : Int) (cyclotomic 2 Int) = 0 := by
    rw [cyclotomic_two]
    norm_num
  have heval := eval_eq_zero_of_dvd_of_eval_eq_zero hresidue hroot
  simp only [z180K6ResiduePolynomial6, eval_add, eval_monomial] at heval
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  norm_num [z180K6ResidueSixSum, hv0, hv1, hv2, hv3, hv4, hv5] at heval
  linarith only [heval]

/-- Integral `Phi_2`, `Phi_6`, and `Phi_18` divisibility annihilates every
alternating modulo-nine fibre. -/
theorem z180_k18_m12_signedNineFiber_zero_of_phi2_phi6_phi18
    (b : Fin 36 → Int)
    (htwo : cyclotomic 2 Int ∣ projection36IndicatorMask b)
    (hsix : cyclotomic 6 Int ∣ projection36IndicatorMask b)
    (heighteen : cyclotomic 18 Int ∣ projection36IndicatorMask b) :
    ∀ r : ZMod 9, z180K18M12SignedNineFiber b r = 0 := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := projection36_phi18_remainders b
    (by simpa [projection36IndicatorMask] using heighteen)
  obtain ⟨f0, f1⟩ :=
    (projection36_phi6_dvd_iff_remainders_zero b).mp hsix
  dsimp only [projection36Phi6R0] at f0
  dsimp only [projection36Phi6R1] at f1
  have p := projection36_phi2_parity_balance b htwo
  let s0 := b 0 + b 18 - b 9 - b 27
  let s1 := b 10 + b 28 - b 1 - b 19
  let s2 := b 2 + b 20 - b 11 - b 29
  let s3 := b 12 + b 30 - b 3 - b 21
  let s4 := b 4 + b 22 - b 13 - b 31
  let s5 := b 14 + b 32 - b 5 - b 23
  let s6 := b 6 + b 24 - b 15 - b 33
  let s7 := b 16 + b 34 - b 7 - b 25
  let s8 := b 8 + b 26 - b 17 - b 35
  have hs06 : s0 = s6 := by
    dsimp only [s0, s6]
    linarith only [e0]
  have hs36 : s3 = s6 := by
    dsimp only [s3, s6]
    linarith only [e3]
  have hs17 : s1 = s7 := by
    dsimp only [s1, s7]
    linarith only [e1]
  have hs47 : s4 = s7 := by
    dsimp only [s4, s7]
    linarith only [e4]
  have hs28 : s2 = s8 := by
    dsimp only [s2, s8]
    linarith only [e2]
  have hs58 : s5 = s8 := by
    dsimp only [s5, s8]
    linarith only [e5]
  have hf0 : s0 - s2 + s3 - s5 + s6 - s8 = 0 := by
    dsimp only [s0, s2, s3, s5, s6, s8]
    linarith only [f0]
  have hf1 : -s1 + s2 - s4 + s5 - s7 + s8 = 0 := by
    dsimp only [s1, s2, s4, s5, s7, s8]
    linarith only [f1]
  have hs02 : s0 = s2 := by
    linarith only [hf0, hs06, hs36, hs28, hs58]
  have hs12 : s1 = s2 := by
    linarith only [hf1, hs17, hs47, hs28, hs58]
  have hsum : s0 + s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 = 0 := by
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8]
    linarith only [p]
  have z0 : s0 = 0 := by
    linarith only [hsum, hs02, hs12, hs06, hs36, hs17, hs47, hs28, hs58]
  have z1 : s1 = 0 := by linarith only [z0, hs02, hs12]
  have z2 : s2 = 0 := by linarith only [z0, hs02]
  have z3 : s3 = 0 := by linarith only [z0, hs06, hs36]
  have z4 : s4 = 0 := by linarith only [z1, hs17, hs47]
  have z5 : s5 = 0 := by linarith only [z2, hs28, hs58]
  have z6 : s6 = 0 := by linarith only [z0, hs06]
  have z7 : s7 = 0 := by linarith only [z1, hs17]
  have z8 : s8 = 0 := by linarith only [z2, hs28]
  intro r
  have hrlt : r.val < 9 := r.val_lt
  interval_cases hv : r.val <;>
    simp only [z180K18M12SignedNineFiber, hv] <;>
    linarith only [z0, z1, z2, z3, z4, z5, z6, z7, z8]

/-- Difference form: if all three exact-order factors divide the difference
of two projected masks, the two alternating fibre profiles agree. -/
theorem z180_k18_m12_signedNineFiber_eq_of_sub_dvd
    (b b' : Fin 36 → Int)
    (htwo : cyclotomic 2 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b')
    (hsix : cyclotomic 6 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b')
    (heighteen : cyclotomic 18 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b') :
    ∀ r : ZMod 9,
      z180K18M12SignedNineFiber b r =
        z180K18M12SignedNineFiber b' r := by
  let d : Fin 36 → Int := fun i => b i - b' i
  have hdmask : projection36IndicatorMask d =
      projection36IndicatorMask b - projection36IndicatorMask b' := by
    simpa [d] using projection36IndicatorMask_sub_order20 b b'
  have hd2 : cyclotomic 2 Int ∣ projection36IndicatorMask d := by
    rw [hdmask]
    exact htwo
  have hd6 : cyclotomic 6 Int ∣ projection36IndicatorMask d := by
    rw [hdmask]
    exact hsix
  have hd18 : cyclotomic 18 Int ∣ projection36IndicatorMask d := by
    rw [hdmask]
    exact heighteen
  have hz := z180_k18_m12_signedNineFiber_zero_of_phi2_phi6_phi18
    d hd2 hd6 hd18
  intro r
  have hr := hz r
  have hrlt : r.val < 9 := r.val_lt
  interval_cases hv : r.val <;>
    simp only [z180K18M12SignedNineFiber, d, hv] at hr ⊢ <;>
    linarith only [hr]

#print axioms projection36_phi2_parity_balance
#print axioms z180_k18_m12_signedNineFiber_zero_of_phi2_phi6_phi18
#print axioms z180_k18_m12_signedNineFiber_eq_of_sub_dvd

end Fuglede
