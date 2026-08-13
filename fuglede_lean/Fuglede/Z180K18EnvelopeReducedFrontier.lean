import Fuglede.Z180K18M2Phi2Phi6Semantic
import Fuglede.Z180K18EnvelopeLevelSizeSemantic

/-!
# Exact remaining finite frontier for the three low-order envelopes

The table-free modules now discharge:

* `(m,q)=(2,6),(2,30)` by the small `Phi_2/Phi_6` remainder kernel and its
  semantic bridge;
* `(2,15),(2,45),(4,15)` by positive level-size arithmetic.

Consequently the still-uninhabited finite boundary is exactly:

* `m=2`: `{18,90}`, the canonical `(2,18)` DP family;
* `m=4`: `{12,36,60,180}`, the canonical `(4,12)` and `(4,36)` DP families;
* `m=12`: `{4,6,18,20,36,45,180}`, the four canonical DP families plus
  the 54-pattern `q=45` table.

This module proves only the logical assembly from those explicit interfaces.
It does not assert an inhabitant for any remaining DP or table.
-/

namespace Fuglede

open Polynomial

/-- The final two `m=2` exclusions, both represented by the canonical
`(2,18)` packed DP. -/
def z180K18M2FinalDPExcludedOrders : Finset Nat := {18, 90}

def Z180K18M2FinalDPEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 2 A L →
    ∀ q ∈ z180K18M2FinalDPExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- The final four `m=4` exclusions, represented by the canonical `(4,12)`
and `(4,36)` packed DP families. -/
def z180K18M4FinalDPExcludedOrders : Finset Nat := {12, 36, 60, 180}

def Z180K18M4FinalDPEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 4 A L →
    ∀ q ∈ z180K18M4FinalDPExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- The three exact residual finite interfaces after all currently
table-free exclusions have been removed. -/
structure Z180K18EnvelopeFinalFrontierInterface : Prop where
  m2DP : Z180K18M2FinalDPEnvelopeInterface
  m4DP : Z180K18M4FinalDPEnvelopeInterface
  m12DPAndPattern : Z180K18M12ResidualEnvelopeInterface

/-- The two remaining DP exclusions plus the two level-size exclusions
inhabit the four-order `m=2` far interface. -/
theorem z180_k18_m2_farResidual_of_finalDP
    (hfinal : Z180K18M2FinalDPEnvelopeInterface) :
    Z180K18M2FarResidualEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq
  simp only [z180K18M2FarResidualExcludedOrders,
    Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact z180_k18_m2_not_phi15_of_level_sizes hcard hcore hdefect
  · exact hfinal A L hSpec hcard hcore hdefect 18
      (by norm_num [z180K18M2FinalDPExcludedOrders])
  · exact z180_k18_m2_not_phi45_of_level_sizes hcard hcore hdefect
  · exact hfinal A L hSpec hcard hcore hdefect 90
      (by norm_num [z180K18M2FinalDPExcludedOrders])

/-- Exact `m=2` residual assembly from only the `(2,18)` DP family. -/
theorem z180_k18_m2_residual_of_finalDP
    (hfinal : Z180K18M2FinalDPEnvelopeInterface) :
    Z180K18M2ResidualEnvelopeInterface :=
  z180_k18_m2_residual_of_far
    (z180_k18_m2_farResidual_of_finalDP hfinal)

/-- Exact public `m=2` envelope assembly from only the `(2,18)` DP family. -/
theorem z180_k18_m2_envelope_of_finalDP
    (hfinal : Z180K18M2FinalDPEnvelopeInterface) :
    Z180K18M2EnvelopeInterface :=
  z180_k18_m2_envelope_of_far
    (z180_k18_m2_farResidual_of_finalDP hfinal)

/-- The four remaining DP exclusions plus the table-free `q=15` theorem
inhabit the five-order `m=4` residual interface. -/
theorem z180_k18_m4_residual_of_finalDP
    (hfinal : Z180K18M4FinalDPEnvelopeInterface) :
    Z180K18M4ResidualEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq
  simp only [z180K18M4ResidualExcludedOrders,
    Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hfinal A L hSpec hcard hcore hdefect 12
      (by norm_num [z180K18M4FinalDPExcludedOrders])
  · exact z180_k18_m4_not_phi15_of_level_sizes hcard hcore hdefect
  · exact hfinal A L hSpec hcard hcore hdefect 36
      (by norm_num [z180K18M4FinalDPExcludedOrders])
  · exact hfinal A L hSpec hcard hcore hdefect 60
      (by norm_num [z180K18M4FinalDPExcludedOrders])
  · exact hfinal A L hSpec hcard hcore hdefect 180
      (by norm_num [z180K18M4FinalDPExcludedOrders])

/-- Exact public `m=4` envelope assembly from the two remaining DP families. -/
theorem z180_k18_m4_envelope_of_finalDP
    (hfinal : Z180K18M4FinalDPEnvelopeInterface) :
    Z180K18M4EnvelopeInterface :=
  z180_k18_m4_envelope_of_residual
    (z180_k18_m4_residual_of_finalDP hfinal)

/-- Honest assembly of all three public envelope interfaces.  The argument
keeps every still-uninhabited DP/pattern certificate visible. -/
def z180K18EnvelopeInterfaces_of_finalFrontier
    (hfinal : Z180K18EnvelopeFinalFrontierInterface) :
    Z180K18EnvelopeInterfaces where
  m2 := z180_k18_m2_envelope_of_finalDP hfinal.m2DP
  m4 := z180_k18_m4_envelope_of_finalDP hfinal.m4DP
  m12 := z180_k18_m12_envelope_of_residual hfinal.m12DPAndPattern

#print axioms z180_k18_m2_farResidual_of_finalDP
#print axioms z180_k18_m2_residual_of_finalDP
#print axioms z180_k18_m2_envelope_of_finalDP
#print axioms z180_k18_m4_residual_of_finalDP
#print axioms z180_k18_m4_envelope_of_finalDP

end Fuglede
