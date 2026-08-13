import Fuglede.Z180K18EnvelopeReducedFrontier

/-!
# Exact split of the residual `m = 12` envelope frontier

Six orders are covered by four paired-remainder DP families.  Order `45`
is the separate finite level-pattern boundary.  This module records only
that split and its logical assembly.
-/

namespace Fuglede

open Polynomial

/-- The six residual orders covered by the four algebraic DP families. -/
def z180K18M12DPExcludedOrders : Finset Nat :=
  {4, 6, 18, 20, 36, 180}

def Z180K18M12DPEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 12 A L →
    ∀ q ∈ z180K18M12DPExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- The sole finite pattern frontier left after the four DP families. -/
def Z180K18M12Phi45EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 12 A L →
    ¬ cyclotomic 45 Int ∣ maskPolynomial 180 A

/-- Exact assembly of the seven-order residual interface from the six DP
orders and the one pattern order. -/
theorem z180_k18_m12_residual_of_dp_phi45
    (hdp : Z180K18M12DPEnvelopeInterface)
    (h45 : Z180K18M12Phi45EnvelopeInterface) :
    Z180K18M12ResidualEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq
  simp only [z180K18M12ResidualExcludedOrders,
    Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hdp A L hSpec hcard hcore hdefect 4
      (by norm_num [z180K18M12DPExcludedOrders])
  · exact hdp A L hSpec hcard hcore hdefect 6
      (by norm_num [z180K18M12DPExcludedOrders])
  · exact hdp A L hSpec hcard hcore hdefect 18
      (by norm_num [z180K18M12DPExcludedOrders])
  · exact hdp A L hSpec hcard hcore hdefect 20
      (by norm_num [z180K18M12DPExcludedOrders])
  · exact hdp A L hSpec hcard hcore hdefect 36
      (by norm_num [z180K18M12DPExcludedOrders])
  · exact h45 A L hSpec hcard hcore hdefect
  · exact hdp A L hSpec hcard hcore hdefect 180
      (by norm_num [z180K18M12DPExcludedOrders])

/-- Public envelope assembly leaving only the explicit `q=45` pattern
interface as an argument. -/
theorem z180_k18_m12_envelope_of_dp_phi45
    (hdp : Z180K18M12DPEnvelopeInterface)
    (h45 : Z180K18M12Phi45EnvelopeInterface) :
    Z180K18M12EnvelopeInterface :=
  z180_k18_m12_envelope_of_residual
    (z180_k18_m12_residual_of_dp_phi45 hdp h45)

#print axioms z180_k18_m12_residual_of_dp_phi45
#print axioms z180_k18_m12_envelope_of_dp_phi45

end Fuglede
