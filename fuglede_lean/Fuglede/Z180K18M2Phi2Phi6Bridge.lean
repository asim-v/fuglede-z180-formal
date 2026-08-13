import Fuglede.Z180K18EnvelopeResidualInterfaces
import Fuglede.Z180K18EnvelopeFiniteKernels

/-!
# Honest semantic boundary around the smallest (k = 18) envelope DP

The finite arithmetic of the canonical `(Phi_2,Phi_6)` packed DP is closed
by `z180_k18_m2_phi2_phi6_pairRemainder_kernel`.  What remains is the
set-to-remainder bridge: projection modulo 36, the nine fibres of size two,
and the integral/mod-five cyclotomic remainders must produce the displayed
bounded integers.  This module names that bridge explicitly and does not
postulate an inhabitant.

Orders 6 and 30 share the same bridge.  For order 6 the second remainder
block is actually zero; weakening it to divisibility by five is sound.
For order 30, reduction modulo five gives the same `Phi_6` block.
-/

namespace Fuglede

open Polynomial

/-- The two exclusions certified by the common `(2,6)` remainder kernel. -/
def z180K18M2Phi2Phi6ExcludedOrders : Finset Nat := {6, 30}

/-- Exact semantic plumbing still required before applying the small
arithmetic kernel.  The last conjunct is precisely the nonzero low-order
remainder supplied by `not Phi_2`. -/
def Z180K18M2Phi2Phi6BridgeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 2 A L →
    ∀ q ∈ z180K18M2Phi2Phi6ExcludedOrders,
      cyclotomic q Int ∣ maskPolynomial 180 A →
      ∃ a b c k2 k60 k61 : Int,
        -3 ≤ a ∧ a ≤ 3 ∧
        -3 ≤ b ∧ b ≤ 3 ∧
        -3 ≤ c ∧ c ≤ 3 ∧
        2 * (a + b + c) = 5 * k2 ∧
        2 * (a - c) = 5 * k60 ∧
        2 * (-b + c) = 5 * k61 ∧
        2 * (a + b + c) ≠ 0

/-- Once the semantic bridge is supplied, both `q=6` and `q=30`
exclusions are kernel consequences of the same six-variable theorem. -/
theorem z180_k18_m2_not_phi6_phi30_of_bridge
    (hbridge : Z180K18M2Phi2Phi6BridgeInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 2 A L) :
    ∀ q ∈ z180K18M2Phi2Phi6ExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A := by
  intro q hq hzero
  obtain ⟨a, b, c, k2, k60, k61,
    haLo, haHi, hbLo, hbHi, hcLo, hcHi,
    h2, h60, h61, h2ne⟩ :=
      hbridge A L hSpec hcard hcore hdefect q hq hzero
  exact z180_k18_m2_phi2_phi6_pairRemainder_kernel
    a b c k2 k60 k61
    haLo haHi hbLo hbHi hcLo hcHi h2 h60 h61 h2ne

/-- After removing the smallest shared DP family, these four exclusions are
the exact remaining `m=2` frontier. -/
def z180K18M2FarResidualExcludedOrders : Finset Nat := {15, 18, 45, 90}

def Z180K18M2FarResidualEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 2 A L →
    ∀ q ∈ z180K18M2FarResidualExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- Glue from the closed `(2,6)` kernel plus the explicit far frontier to
the six-order residual interface used by the envelope assembler. -/
theorem z180_k18_m2_residual_of_phi2Phi6Bridge
    (hbridge : Z180K18M2Phi2Phi6BridgeInterface)
    (hfar : Z180K18M2FarResidualEnvelopeInterface) :
    Z180K18M2ResidualEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq
  have hsmall := z180_k18_m2_not_phi6_phi30_of_bridge
    hbridge hSpec hcard hcore hdefect
  simp only [z180K18M2ResidualExcludedOrders, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsmall 6 (by norm_num [z180K18M2Phi2Phi6ExcludedOrders])
  · exact hfar A L hSpec hcard hcore hdefect 15
      (by norm_num [z180K18M2FarResidualExcludedOrders])
  · exact hfar A L hSpec hcard hcore hdefect 18
      (by norm_num [z180K18M2FarResidualExcludedOrders])
  · exact hsmall 30 (by norm_num [z180K18M2Phi2Phi6ExcludedOrders])
  · exact hfar A L hSpec hcard hcore hdefect 45
      (by norm_num [z180K18M2FarResidualExcludedOrders])
  · exact hfar A L hSpec hcard hcore hdefect 90
      (by norm_num [z180K18M2FarResidualExcludedOrders])

#print axioms z180_k18_m2_not_phi6_phi30_of_bridge
#print axioms z180_k18_m2_residual_of_phi2Phi6Bridge

end Fuglede
