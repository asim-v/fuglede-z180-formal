import Fuglede.Z180K30CommonSpectrumCompatibility
import Fuglede.Z180K30Fibres

/-!
# Narrow certificate interface for the `k = 30` common spectrum

The generated arithmetic proof should not be imported into the structural
fibre code.  Its exact semantic output is the zero-descent predicate below:
the fixed zeroth fibre of `L`, projected to `ZMod 36`, annihilates every one
of the five projected fibres of `A` at all of its nonzero differences.

This file proves that this output is precisely enough to construct the
common `ZMod 36` spectrum expected by `Z180K30CommonSpectrumCompatibility`.
It deliberately does not provide a term of the certificate type.
-/

namespace Fuglede

/-- `Fin 5`-indexed spelling expected by the common-spectrum endpoint. -/
noncomputable def z180K30FifthFibres36
    (X : Finset (ZMod 180)) (i : Fin 5) : Finset (ZMod 36) :=
  z180K30Fibre X (i.val : ZMod 5)

/-- The exact common orthogonality conclusion to be produced after the nine
bad-signature arithmetic cases have been discharged. -/
def Z180K30FifthFibresZeroDescend
    (A L : Finset (ZMod 180)) : Prop :=
  ∀ i : Fin 5,
    ∀ l₁ ∈ z180K30FifthFibres36 L (0 : Fin 5),
    ∀ l₂ ∈ z180K30FifthFibres36 L (0 : Fin 5), l₁ ≠ l₂ →
      CyclotomicZero 36 (z180K30FifthFibres36 A i) (l₁ - l₂)

/-- Stable theorem type for a generated joint QF_LIA adapter.  No theorem in
the source tree asserts this proposition until the nine UNSAT certificates
are actually materialized. -/
def Z180K30JointQFLIAZeroDescentCertificate : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L → A.card = 30 →
      Z180K30FifthFibresZeroDescend A L

/-- Zero descent, together with the already sealed order-five balance, gives
one genuine six-point spectrum shared by all five `A` fibres. -/
theorem z180_k30_five_fibres_common_spectrum_of_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hdesc : Z180K30FifthFibresZeroDescend A L) :
    Z180K30FiveFibresHaveCommonZ36Spectrum
      (z180K30FifthFibres36 A)
      (z180K30FifthFibres36 L (0 : Fin 5)) := by
  have hcardA := z180_k30_fibre_card_six hSpec hcard
  have hcardL := z180_k30_fibre_card_six
    (cyclotomicSpectrum_dual hSpec) (hSpec.2.1.symm.trans hcard)
  intro i
  have hAi : (z180K30FifthFibres36 A i).card = 6 := by
    exact hcardA (i.val : ZMod 5)
  have hL0 : (z180K30FifthFibres36 L (0 : Fin 5)).card = 6 := by
    exact hcardL (0 : ZMod 5)
  refine ⟨Finset.card_pos.mp (by omega), hAi.trans hL0.symm, ?_⟩
  exact hdesc i

/-- The generated certificate plugs into the common-spectrum endpoint with
no additional arithmetic premise. -/
theorem z180_k30_five_fibres_common_spectrum_of_joint_qflia_certificate
    (hcert : Z180K30JointQFLIAZeroDescentCertificate)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    Z180K30FiveFibresHaveCommonZ36Spectrum
      (z180K30FifthFibres36 A)
      (z180K30FifthFibres36 L (0 : Fin 5)) := by
  exact z180_k30_five_fibres_common_spectrum_of_zero_descent
    hSpec hcard (hcert A L hSpec hcard)

/-- Consequently the same single complement tiles all five projected
fibres.  This is still conditional on the materialized joint certificate. -/
theorem z180_k30_five_fibres_common_complement_of_joint_qflia_certificate
    (hcert : Z180K30JointQFLIAZeroDescentCertificate)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    ∃ B : Finset (ZMod 36),
      ∀ i, Tiles (z180K30FifthFibres36 A i) B := by
  have hcardA := z180_k30_fibre_card_six hSpec hcard
  apply z180_k30_five_fibres_common_complement_of_common_spectrum
    (A := z180K30FifthFibres36 A)
    (L := z180K30FifthFibres36 L (0 : Fin 5))
  · intro i
    exact hcardA (i.val : ZMod 5)
  · exact z180_k30_five_fibres_common_spectrum_of_joint_qflia_certificate
      hcert hSpec hcard

end Fuglede
