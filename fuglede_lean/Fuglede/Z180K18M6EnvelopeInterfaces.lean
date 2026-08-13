import Fuglede.Z180K18M6Terminal
import Fuglede.Z180K18EnvelopeResidualInterfaces
import Fuglede.Z180DivisorCases
import Mathlib.Tactic

/-!
# Exact finite boundary of the `k = 18`, `m = 6` envelope

Seven excluded orders belong to four paired-remainder DP families.  Order
45 is the separate level-pattern frontier.  Orders five and six are already
excluded respectively by cardinality and by the missing base factor in the
defect.  This module records the honest split and all logical assembly; it
does not introduce inhabitants of the DP or pattern interfaces.
-/

namespace Fuglede

open Polynomial

/-- Orders covered by the four `m = 6` paired-remainder families. -/
def z180K18M6DPExcludedOrders : Finset Nat :=
  {2, 10, 12, 18, 36, 60, 90}

def Z180K18M6DPEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 6 A L →
    ∀ q ∈ z180K18M6DPExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

def Z180K18M6Phi45EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 6 A L →
    ¬ cyclotomic 45 Int ∣ maskPolynomial 180 A

/-- Assemble the full seven-order envelope from the exact DP and `q=45`
frontiers plus the two elementary exclusions. -/
theorem z180_k18_m6_envelope_of_dp_phi45
    (hdp : Z180K18M6DPEnvelopeInterface)
    (h45 : Z180K18M6Phi45EnvelopeInterface) :
    Z180K18M6EnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect
  intro q hqdiv hqgt hqzero
  rcases dvd_180_cases (by omega) hqdiv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 2
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · norm_num [z180K18M6EnvelopeOrders]
  · norm_num [z180K18M6EnvelopeOrders]
  · exact False.elim
      ((z180_k18_not_cyclotomic_five_of_card hcard) hqzero)
  · exact False.elim
      ((z180_k18_not_base_factor_of_fiveFactorDefect hdefect) hqzero)
  · norm_num [z180K18M6EnvelopeOrders]
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 10
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 12
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · norm_num [z180K18M6EnvelopeOrders]
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 18
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · norm_num [z180K18M6EnvelopeOrders]
  · norm_num [z180K18M6EnvelopeOrders]
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 36
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · exact False.elim ((h45 A L hSpec hcard hcore hdefect) hqzero)
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 60
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · exact False.elim
      ((hdp A L hSpec hcard hcore hdefect 90
        (by norm_num [z180K18M6DPExcludedOrders])) hqzero)
  · norm_num [z180K18M6EnvelopeOrders]

#print axioms z180_k18_m6_envelope_of_dp_phi45

end Fuglede
