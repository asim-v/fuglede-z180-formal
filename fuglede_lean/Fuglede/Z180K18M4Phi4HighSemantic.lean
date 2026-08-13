import Fuglede.Z180K18EnvelopeReducedFrontier
import Fuglede.Z180K12M6Order20Phi4
import Fuglede.Z180K12M6HighOrderRemainders3_12Shard
import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard
import Mathlib.Tactic

/-!
# Semantic closure of the final `m = 4` envelope frontier

The four residual orders split into the two canonical DP families
`(4,12)` and `(4,36)`, but neither family needs an enumerated table.

For `(4,12)`, the projected `Phi_4` block and the four `Phi_12`
coordinates become two independent three-variable systems.  Every
variable is a sum of three differences of zero-one occupancies, hence lies
in `[-3,3]`; the relevant coefficient matrices are invertible modulo five.

For `(4,36)`, the twelve `Phi_36` coordinates are differences of pairs of
local `Phi_4` balances.  Their absolute values are at most two, so reduction
modulo five already makes them zero.  They identify three triples of local
balances, and the nonzero `Phi_4` block supplied by the defect is forced to
vanish.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- First explicit coefficient of the projected remainder modulo `Phi_4`. -/
def z180K18ProjectionPhi4R0 (b : Fin 36 → Int) : Int :=
  z180K12Order20Phi4R0 (projection36Count12 b)

/-- Second explicit coefficient of the projected remainder modulo `Phi_4`. -/
def z180K18ProjectionPhi4R1 (b : Fin 36 → Int) : Int :=
  z180K12Order20Phi4R1 (projection36Count12 b)

/-- The generic monic-remainder coefficients at order four are the two
alternating mod-four balances. -/
theorem projection36_phi4_remainder_coeffs (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 4 b 0 =
        z180K18ProjectionPhi4R0 b ∧
      projection36CyclotomicRemainderCoeff 4 b 1 =
        z180K18ProjectionPhi4R1 b := by
  let r := projection36RemainderRemoved 4 b
  have hdiv : cyclotomic 4 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 4 b (by
      rw [show Nat.totient 4 = 2 by decide]
      norm_num)
  obtain ⟨h0, h1⟩ := projection36_phi4_count12_remainders_order20 r hdiv
  have hz (j : Nat) (hj : 2 ≤ j) :
      projection36CyclotomicRemainderCoeff 4 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 4 = 2 by decide]
    exact hj
  constructor
  · dsimp only [z180K18ProjectionPhi4R0,
      z180K12Order20Phi4R0, projection36Count12, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  · dsimp only [z180K18ProjectionPhi4R1,
      z180K12Order20Phi4R1, projection36Count12, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith

/-- A mapped `Phi_4` divisor makes both displayed integral coefficients
multiples of five. -/
theorem projection36_phi4_five_multipliers
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 4 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 : Int,
      z180K18ProjectionPhi4R0 b = 5 * k0 ∧
      z180K18ProjectionPhi4R1 b = 5 * k1 := by
  obtain ⟨k0, hk0⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  rcases projection36_phi4_remainder_coeffs b with ⟨h0, h1⟩
  exact ⟨k0, k1, h0.symm.trans hk0, h1.symm.trans hk1⟩

/-- The canonical `(4,12)` and `(4,36)` arithmetic closes all four final
`m = 4` orders. -/
theorem z180_k18_m4_finalDP :
    Z180K18M4FinalDPEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq hqzero
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  have hlo : ∀ i : Fin 36, 0 ≤ b i := by
    intro i
    exact z180K12ProjectionIndicator_nonneg A i
  have hinj0 := z180_k18_projection36_injOn hSpec hcard
  have hinj :
      Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
        (A : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply hinj0 hx hy
    simpa only [z180K18Projection36_apply] using hxy
  have hhi : ∀ i : Fin 36, b i ≤ 1 := by
    intro i
    exact z180K12ProjectionIndicator_le_one_of_injOn hinj i

  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder, h20, hnot4⟩ := hdefect
  have hmod4 :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 4) (by norm_num) (by norm_num) (by simpa using h20)
  obtain ⟨k40, k41, hk40, hk41⟩ :=
    projection36_phi4_five_multipliers b hmod4
  rcases projection36_phi4_remainder_coeffs b with ⟨hcoeff40, hcoeff41⟩
  have hnotIndicator :
      ¬ cyclotomic 4 Int ∣ projection36IndicatorMask b := by
    intro hind
    apply hnot4
    apply (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (m := 4) (by norm_num)).1
    simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator] using hind
  have hphi4NotBothZero :
      ¬ (z180K18ProjectionPhi4R0 b = 0 ∧
        z180K18ProjectionPhi4R1 b = 0) := by
    intro hz
    apply hnotIndicator
    apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero b
    intro j hj
    rw [show Nat.totient 4 = 2 by decide] at hj
    interval_cases j
    · exact hcoeff40.trans hz.1
    · exact hcoeff41.trans hz.2

  let x0 : Int := b 0 - b 18
  let y0 : Int := b 9 - b 27
  let x1 : Int := b 28 - b 10
  let y1 : Int := b 1 - b 19
  let x2 : Int := b 20 - b 2
  let y2 : Int := b 29 - b 11
  let x3 : Int := b 12 - b 30
  let y3 : Int := b 21 - b 3
  let x4 : Int := b 4 - b 22
  let y4 : Int := b 13 - b 31
  let x5 : Int := b 32 - b 14
  let y5 : Int := b 5 - b 23
  let x6 : Int := b 24 - b 6
  let y6 : Int := b 33 - b 15
  let x7 : Int := b 16 - b 34
  let y7 : Int := b 25 - b 7
  let x8 : Int := b 8 - b 26
  let y8 : Int := b 17 - b 35

  have hdiff (i j : Fin 36) :
      -1 ≤ b i - b j ∧ b i - b j ≤ 1 := by
    have hilo : 0 ≤ b i := hlo i
    have hihi : b i ≤ 1 := hhi i
    have hjlo : 0 ≤ b j := hlo j
    have hjhi : b j ≤ 1 := hhi j
    constructor <;> omega
  obtain ⟨hx0lo, hx0hi⟩ := hdiff 0 18
  obtain ⟨hy0lo, hy0hi⟩ := hdiff 9 27
  obtain ⟨hx1lo, hx1hi⟩ := hdiff 28 10
  obtain ⟨hy1lo, hy1hi⟩ := hdiff 1 19
  obtain ⟨hx2lo, hx2hi⟩ := hdiff 20 2
  obtain ⟨hy2lo, hy2hi⟩ := hdiff 29 11
  obtain ⟨hx3lo, hx3hi⟩ := hdiff 12 30
  obtain ⟨hy3lo, hy3hi⟩ := hdiff 21 3
  obtain ⟨hx4lo, hx4hi⟩ := hdiff 4 22
  obtain ⟨hy4lo, hy4hi⟩ := hdiff 13 31
  obtain ⟨hx5lo, hx5hi⟩ := hdiff 32 14
  obtain ⟨hy5lo, hy5hi⟩ := hdiff 5 23
  obtain ⟨hx6lo, hx6hi⟩ := hdiff 24 6
  obtain ⟨hy6lo, hy6hi⟩ := hdiff 33 15
  obtain ⟨hx7lo, hx7hi⟩ := hdiff 16 34
  obtain ⟨hy7lo, hy7hi⟩ := hdiff 25 7
  obtain ⟨hx8lo, hx8hi⟩ := hdiff 8 26
  obtain ⟨hy8lo, hy8hi⟩ := hdiff 17 35

  let X0 : Int := x0 + x3 + x6
  let X1 : Int := x1 + x4 + x7
  let X2 : Int := x2 + x5 + x8
  let Y0 : Int := y0 + y3 + y6
  let Y1 : Int := y1 + y4 + y7
  let Y2 : Int := y2 + y5 + y8
  have hX0lo : -3 ≤ X0 := by
    dsimp only [X0, x0, x3, x6]
    omega
  have hX0hi : X0 ≤ 3 := by
    dsimp only [X0, x0, x3, x6]
    omega
  have hX1lo : -3 ≤ X1 := by
    dsimp only [X1, x1, x4, x7]
    omega
  have hX1hi : X1 ≤ 3 := by
    dsimp only [X1, x1, x4, x7]
    omega
  have hX2lo : -3 ≤ X2 := by
    dsimp only [X2, x2, x5, x8]
    omega
  have hX2hi : X2 ≤ 3 := by
    dsimp only [X2, x2, x5, x8]
    omega
  have hY0lo : -3 ≤ Y0 := by
    dsimp only [Y0, y0, y3, y6]
    omega
  have hY0hi : Y0 ≤ 3 := by
    dsimp only [Y0, y0, y3, y6]
    omega
  have hY1lo : -3 ≤ Y1 := by
    dsimp only [Y1, y1, y4, y7]
    omega
  have hY1hi : Y1 ≤ 3 := by
    dsimp only [Y1, y1, y4, y7]
    omega
  have hY2lo : -3 ≤ Y2 := by
    dsimp only [Y2, y2, y5, y8]
    omega
  have hY2hi : Y2 ≤ 3 := by
    dsimp only [Y2, y2, y5, y8]
    omega

  have hR40 : z180K18ProjectionPhi4R0 b = X0 + X1 + X2 := by
    change
      ((b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) +
        (b 4 + b 16 + b 28) - (b 6 + b 18 + b 30) +
        (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34)) =
          X0 + X1 + X2
    dsimp only [X0, X1, X2, x0, x1, x2, x3, x4, x5, x6, x7, x8]
    ring
  have hR41 : z180K18ProjectionPhi4R1 b = Y0 + Y1 + Y2 := by
    change
      ((b 1 + b 13 + b 25) - (b 3 + b 15 + b 27) +
        (b 5 + b 17 + b 29) - (b 7 + b 19 + b 31) +
        (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35)) =
          Y0 + Y1 + Y2
    dsimp only [Y0, Y1, Y2, y0, y1, y2, y3, y4, y5, y6, y7, y8]
    ring
  have hR120 : Z180K12HighOrder.projection36Phi12R0 b = X0 - X1 := by
    change
      ((b 0 + b 12 + b 24) - (b 4 + b 16 + b 28) -
        (b 6 + b 18 + b 30) + (b 10 + b 22 + b 34)) = X0 - X1
    dsimp only [X0, X1, x0, x1, x3, x4, x6, x7]
    ring
  have hR121 : Z180K12HighOrder.projection36Phi12R1 b = Y1 - Y2 := by
    change
      ((b 1 + b 13 + b 25) - (b 5 + b 17 + b 29) -
        (b 7 + b 19 + b 31) + (b 11 + b 23 + b 35)) = Y1 - Y2
    dsimp only [Y1, Y2, y1, y2, y4, y5, y7, y8]
    ring
  have hR122 : Z180K12HighOrder.projection36Phi12R2 b = X1 - X2 := by
    change
      ((b 2 + b 14 + b 26) + (b 4 + b 16 + b 28) -
        (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34)) = X1 - X2
    dsimp only [X1, X2, x1, x2, x4, x5, x7, x8]
    ring
  have hR123 : Z180K12HighOrder.projection36Phi12R3 b = -Y0 + Y2 := by
    change
      ((b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) -
        (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35)) = -Y0 + Y2
    dsimp only [Y0, Y2, y0, y2, y3, y5, y6, y8]
    ring

  have close12 :
      (∃ k120 k121 k122 k123 : Int,
        Z180K12HighOrder.projection36Phi12R0 b = 5 * k120 ∧
        Z180K12HighOrder.projection36Phi12R1 b = 5 * k121 ∧
        Z180K12HighOrder.projection36Phi12R2 b = 5 * k122 ∧
        Z180K12HighOrder.projection36Phi12R3 b = 5 * k123) → False := by
    rintro ⟨k120, k121, k122, k123, hk120, hk121, hk122, hk123⟩
    have hx0 : X0 = 0 := by omega
    have hx1 : X1 = 0 := by omega
    have hx2 : X2 = 0 := by omega
    have hy0 : Y0 = 0 := by omega
    have hy1 : Y1 = 0 := by omega
    have hy2 : Y2 = 0 := by omega
    apply hphi4NotBothZero
    constructor
    · rw [hR40, hx0, hx1, hx2]
      norm_num
    · rw [hR41, hy0, hy1, hy2]
      norm_num

  have close36 :
      (Z180K12HighOrder.projection36Phi36R0 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R1 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R2 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R3 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R4 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R5 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R6 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R7 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R8 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R9 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R10 b = 0 ∧
        Z180K12HighOrder.projection36Phi36R11 b = 0) → False := by
    rintro ⟨hr0, hr1, hr2, hr3, hr4, hr5,
      hr6, hr7, hr8, hr9, hr10, hr11⟩
    have hx03 : x0 = x3 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R0, x0, x3] at hr0 ⊢
      omega
    have hx36 : x3 = x6 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R6, x3, x6] at hr6 ⊢
      omega
    have hx17 : x1 = x7 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R10, x1, x7] at hr10 ⊢
      omega
    have hx47 : x4 = x7 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R4, x4, x7] at hr4 ⊢
      omega
    have hx25 : x2 = x5 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R2, x2, x5] at hr2 ⊢
      omega
    have hx58 : x5 = x8 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R8, x5, x8] at hr8 ⊢
      omega
    have hy14 : y1 = y4 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R1, y1, y4] at hr1 ⊢
      omega
    have hy47 : y4 = y7 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R7, y4, y7] at hr7 ⊢
      omega
    have hy36 : y3 = y6 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R3, y3, y6] at hr3 ⊢
      omega
    have hy06 : y0 = y6 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R9, y0, y6] at hr9 ⊢
      omega
    have hy58 : y5 = y8 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R5, y5, y8] at hr5 ⊢
      omega
    have hy28 : y2 = y8 := by
      dsimp only [Z180K12HighOrder.projection36Phi36R11, y2, y8] at hr11 ⊢
      omega
    have hR40triple :
        z180K18ProjectionPhi4R0 b = 3 * (x0 + x1 + x2) := by
      rw [hR40]
      dsimp only [X0, X1, X2]
      omega
    have hR41triple :
        z180K18ProjectionPhi4R1 b = 3 * (y0 + y1 + y2) := by
      rw [hR41]
      dsimp only [Y0, Y1, Y2]
      omega
    have h40zero : z180K18ProjectionPhi4R0 b = 0 := by
      omega
    have h41zero : z180K18ProjectionPhi4R1 b = 0 := by
      omega
    exact hphi4NotBothZero ⟨h40zero, h41zero⟩

  simp only [z180K18M4FinalDPExcludedOrders, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · have hprojected : cyclotomic 12 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 12) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 12 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi12_count12_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    rcases hraw with ⟨hr0, hr1, hr2, hr3⟩
    apply close12
    exact ⟨0, 0, 0, 0,
      by simpa [Z180K12HighOrder.projection36Phi12R0] using hr0,
      by simpa [Z180K12HighOrder.projection36Phi12R1] using hr1,
      by simpa [Z180K12HighOrder.projection36Phi12R2] using hr2,
      by simpa [Z180K12HighOrder.projection36Phi12R3] using hr3⟩
  · have hprojected : cyclotomic 36 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 36) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi36_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    apply close36
    simpa only [Z180K12HighOrder.projection36Phi36R0,
      Z180K12HighOrder.projection36Phi36R1,
      Z180K12HighOrder.projection36Phi36R2,
      Z180K12HighOrder.projection36Phi36R3,
      Z180K12HighOrder.projection36Phi36R4,
      Z180K12HighOrder.projection36Phi36R5,
      Z180K12HighOrder.projection36Phi36R6,
      Z180K12HighOrder.projection36Phi36R7,
      Z180K12HighOrder.projection36Phi36R8,
      Z180K12HighOrder.projection36Phi36R9,
      Z180K12HighOrder.projection36Phi36R10,
      Z180K12HighOrder.projection36Phi36R11] using hraw
  · have hmod12 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 12) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact close12
      (Z180K12HighOrder.projection36_phi12_five_multipliers_high b hmod12)
  · have hmod36 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 36) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact close36
      (Z180K12HighOrder.projection36_phi36_remainders_zero_of_mod_five_dvd_high
        b hlo hhi hmod36)

/-- Public `m = 4` envelope assembled from the closed final frontier. -/
theorem z180_k18_m4_envelope : Z180K18M4EnvelopeInterface :=
  z180_k18_m4_envelope_of_finalDP z180_k18_m4_finalDP

#print axioms projection36_phi4_remainder_coeffs
#print axioms projection36_phi4_five_multipliers
#print axioms z180_k18_m4_finalDP
#print axioms z180_k18_m4_envelope

end Fuglede
