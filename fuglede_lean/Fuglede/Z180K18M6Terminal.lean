import Fuglede.Z180K18LowOrderInterfaces
import Fuglede.Z180K18M6GraphStructural
import Mathlib.Tactic

/-!
# Terminal assembly for the cardinality-eighteen `m = 6` branch

The structural Cayley-graph argument proves that a set whose nonzero
differences have orders in `{3,4,9,15,20,30,180}` has cardinality at most
nine.  This module connects that theorem to spectral orthogonality.

The only remaining input is the exact mask-zero envelope computed by the
finite audit.  It is exposed as a `Prop` interface; this file introduces no
axiom and asserts no inhabitant of that interface.
-/

namespace Fuglede

/-- The exact zero-order envelope for the `m = 6` defect branch. -/
def z180K18M6EnvelopeOrders : Finset Nat :=
  {3, 4, 9, 15, 20, 30, 180}

/-- Semantic completeness of the exact `m = 6` mask-zero envelope. -/
def Z180K18M6EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 6 A L →
    Z180K18MaskZeroOrderEnvelope A z180K18M6EnvelopeOrders

/-- Spectral orthogonality turns the exact mask-zero envelope into the
pairwise-allowed predicate used by the structural graph theorem. -/
theorem z180_k18_m6_pairwiseAllowed_of_maskZeroEnvelope
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (henvelope :
      Z180K18MaskZeroOrderEnvelope A z180K18M6EnvelopeOrders) :
    Z180K18M6PairwiseAllowed L := by
  have hdiff :
      Z180K18DifferenceOrderEnvelope L z180K18M6EnvelopeOrders :=
    z180_k18_differenceOrderEnvelope_of_maskZeroOrderEnvelope
      hSpec henvelope
  intro x hx y hy hne
  constructor
  · exact sub_ne_zero.mpr hne
  · have hmem := hdiff x hx y hy hne
    simpa [z180K18M6EnvelopeOrders] using hmem

/-- Envelope completeness contradicts an `m = 6` defect: the spectrum has
cardinality eighteen, whereas the exact envelope graph has clique number at
most nine. -/
theorem z180_k18_no_m6_defect_of_envelope
    (henvelope : Z180K18M6EnvelopeInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 6 A L) : False := by
  have hcardL : L.card = 18 := hSpec.2.1.symm.trans hcard
  have hmaskEnvelope := henvelope A L hSpec hcard hcore hdefect
  have hpair :=
    z180_k18_m6_pairwiseAllowed_of_maskZeroEnvelope hSpec hmaskEnvelope
  have hle := z180_k18_m6_card_le_nine_of_pairwise_allowed L hpair
  omega

/-- Conditional terminal certificate for the `m = 6` branch. -/
theorem z180_k18_terminal_branch_six_of_envelope
    (henvelope : Z180K18M6EnvelopeInterface) :
    Z180K18TerminalBranchCertificate 6 := by
  intro A L hSpec hcard hcore hdefect
  exact False.elim
    (z180_k18_no_m6_defect_of_envelope
      henvelope hSpec hcard hcore hdefect)

#print axioms z180_k18_m6_pairwiseAllowed_of_maskZeroEnvelope
#print axioms z180_k18_no_m6_defect_of_envelope
#print axioms z180_k18_terminal_branch_six_of_envelope

end Fuglede
