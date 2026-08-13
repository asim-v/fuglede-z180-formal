import Fuglede.ExactOrderEnergy
import Fuglede.Z180K30CommonSpectrumInterface
import Fuglede.Z180K30FibreFourier
import Mathlib.Tactic

/-!
# Exact-order closure implies the `k = 30` common spectrum

The arithmetic certificate need only prove one integer statement: every
nonzero difference occurring in the fixed zeroth fifth-coordinate fibre of
`L`, of exact order `m`, is accompanied somewhere in `L` by positive
exact-order mass at `5m`.

Spectral complementarity then gives order-`m` and order-`5m` Fourier zeros
on `A`.  The five-level DFT identity makes all five fibre sums equal, while
the order-`m` zero makes their sum zero.  Hence every fibre sum vanishes.
-/

namespace Fuglede

open scoped BigOperators

/-- Purely integer conclusion expected from the nine bad-signature cases. -/
def Z180K30ZerothFibreFivefoldOrderClosure
    (L : Finset (ZMod 180)) : Prop :=
  ∀ y₁ ∈ z180K30FifthSlice L (0 : ZMod 5),
    ∀ y₂ ∈ z180K30FifthSlice L (0 : ZMod 5), y₁ ≠ y₂ →
      0 < exactOrderDistributionInt L
        (frequencyOrder 180 (y₁ - y₂) * 5)

/-- Stable arithmetic theorem type for a generated joint QF_LIA adapter.
This source module intentionally does not construct a term of this type. -/
def Z180K30JointQFLIAOrderClosureCertificate : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L → A.card = 30 →
      Z180K30ZerothFibreFivefoldOrderClosure L

/-- The exact-order closure is sufficient for common zero descent. -/
theorem z180_k30_zero_descent_of_fivefold_order_closure
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hclose : Z180K30ZerothFibreFivefoldOrderClosure L) :
    Z180K30FifthFibresZeroDescend A L := by
  intro i l₁ hl₁ l₂ hl₂ hlne
  change l₁ ∈ z180K30Fibre L (0 : ZMod 5) at hl₁
  change l₂ ∈ z180K30Fibre L (0 : ZMod 5) at hl₂
  rw [z180K30Fibre] at hl₁ hl₂
  obtain ⟨y₁, hy₁F, rfl⟩ := Finset.mem_image.mp hl₁
  obtain ⟨y₂, hy₂F, rfl⟩ := Finset.mem_image.mp hl₂
  have hy₁L : y₁ ∈ L := (Finset.mem_filter.mp hy₁F).1
  have hy₂L : y₂ ∈ L := (Finset.mem_filter.mp hy₂F).1
  have hy₁five : (ZMod.cast y₁ : ZMod 5) = 0 :=
    (Finset.mem_filter.mp hy₁F).2
  have hy₂five : (ZMod.cast y₂ : ZMod 5) = 0 :=
    (Finset.mem_filter.mp hy₂F).2
  have hyne : y₁ ≠ y₂ := by
    intro h
    subst y₂
    exact hlne rfl
  let δ : ZMod 180 := y₁ - y₂
  let d : ZMod 36 := z180K30Projection36 y₁ - z180K30Projection36 y₂
  let m : ℕ := frequencyOrder 180 δ
  have hδfive : (ZMod.cast δ : ZMod 5) = 0 := by
    dsimp only [δ]
    rw [ZMod.cast_sub (by norm_num : 5 ∣ 180),
      hy₁five, hy₂five, sub_self]
  have hprojectedOrder : frequencyOrder 36 d = m := by
    have h :=
      z180_frequencyOrder_eq_projection36_of_fifthCoordinate_zero δ hδfive
    rw [map_sub] at h
    exact h.symm
  have hδne : δ ≠ 0 := by
    exact sub_ne_zero.mpr hyne
  have hmpos : 0 < m := by
    dsimp only [m]
    rw [frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos δ
  have hmne : m ≠ 1 := by
    intro hm
    apply hδne
    apply (frequencyOrder_eq_one_iff (by norm_num) δ).mp
    simpa only [m] using hm
  have hlowZero : CyclotomicZero 180 A δ :=
    hSpec.2.2 y₁ hy₁L y₂ hy₂L hyne
  have hlowEnergy : exactOrderFourierEnergy A m = 0 :=
    exactOrderFourierEnergy_eq_zero_of_cyclotomicZero (by rfl) hlowZero
  have hlowOrbit :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero A m).mp hlowEnergy
  let e : ZMod 180 := z180K30LiftFrequency36 d
  let u : CRT180 := toCRT180 e
  have heOrder : frequencyOrder 180 e = m := by
    dsimp only [e]
    rw [frequencyOrder_z180K30LiftFrequency36]
    exact hprojectedOrder
  have huFive : crt180FifthCoord u = 0 := by
    simpa only [u, e] using z180K30LiftFrequency36_fifthCoord d
  have hbaseZero : CyclotomicZero 180 A e := hlowOrbit e heOrder
  have hbaseFourier : fourierSum A e = 0 :=
    (cyclotomicZero_iff_fourierSum_zero A e).mp hbaseZero
  have hbaseCRT : z180StandardCRTFourierSum A u = 0 := by
    rw [z180StandardCRTFourierSum_eq_fourierSum]
    simpa only [u, e, fromCRT180_toCRT180] using hbaseFourier
  have hhighPosInt :
      0 < exactOrderDistributionInt L (m * 5) := by
    simpa only [m, δ] using hclose y₁ hy₁F y₂ hy₂F hyne
  have hhighPosNat : 0 < exactOrderDistribution L (m * 5) := by
    rw [exactOrderDistributionInt] at hhighPosInt
    exact_mod_cast hhighPosInt
  have hhighEnergy : exactOrderFourierEnergy A (m * 5) = 0 :=
    exactOrderFourierEnergy_A_eq_zero_of_distribution_L_pos
      hSpec (by omega) hhighPosNat
  have hhighOrbit :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero A (m * 5)).mp
      hhighEnergy
  have hlevelsEqual : ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum A u c =
        z180FiveLevelFourierSum A u c' := by
    apply z180FiveLevelFourierSum_eq_of_cyclotomicZero_extensions A u
    intro b hb
    apply hhighOrbit
    calc
      frequencyOrder 180
          (fromCRT180 (u + crt180FifthSingle (-b))) =
          frequencyOrder 180 (fromCRT180 u) * 5 :=
        frequencyOrder_fromCRT180_add_fifth u huFive (neg_ne_zero.mpr hb)
      _ = m * 5 := by
        rw [show fromCRT180 u = e by simp only [u, fromCRT180_toCRT180],
          heOrder]
  have hsumZero :
      (∑ c : ZMod 5, z180FiveLevelFourierSum A u c) = 0 := by
    rw [sum_z180FiveLevelFourierSum_eq]
    exact hbaseCRT
  have hlevelZero : ∀ c : ZMod 5,
      z180FiveLevelFourierSum A u c = 0 := by
    intro c
    have hsumConst :
        (∑ c' : ZMod 5, z180FiveLevelFourierSum A u c') =
          (5 : ℂ) * z180FiveLevelFourierSum A u c := by
      calc
        _ = ∑ _c' : ZMod 5, z180FiveLevelFourierSum A u c := by
          apply Finset.sum_congr rfl
          intro c' hc'
          exact hlevelsEqual c' c
        _ = (5 : ℂ) * z180FiveLevelFourierSum A u c := by simp
    have hmul : (5 : ℂ) * z180FiveLevelFourierSum A u c = 0 := by
      rw [← hsumConst]
      exact hsumZero
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  change CyclotomicZero 36
    (z180K30Fibre A (i.val : ZMod 5)) d
  apply (cyclotomicZero_iff_fourierSum_zero _ _).mpr
  rw [fourierSum_z180K30FifthFiber36]
  simpa only [u, e] using hlevelZero (i.val : ZMod 5)

/-- An arithmetic certificate produces the exact zero-descent certificate
consumed by the common-spectrum interface. -/
theorem z180K30JointQFLIAZeroDescentCertificate_of_orderClosureCertificate
    (hcert : Z180K30JointQFLIAOrderClosureCertificate) :
    Z180K30JointQFLIAZeroDescentCertificate := by
  intro A L hSpec hcard
  exact z180_k30_zero_descent_of_fivefold_order_closure
    hSpec (hcert A L hSpec hcard)

/-- Direct conditional endpoint from the arithmetic certificate to the
common `ZMod 36` spectrum. -/
theorem z180_k30_five_fibres_common_spectrum_of_orderClosureCertificate
    (hcert : Z180K30JointQFLIAOrderClosureCertificate)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    Z180K30FiveFibresHaveCommonZ36Spectrum
      (z180K30FifthFibres36 A)
      (z180K30FifthFibres36 L (0 : Fin 5)) := by
  apply z180_k30_five_fibres_common_spectrum_of_joint_qflia_certificate
    (z180K30JointQFLIAZeroDescentCertificate_of_orderClosureCertificate hcert)
    hSpec hcard

end Fuglede
