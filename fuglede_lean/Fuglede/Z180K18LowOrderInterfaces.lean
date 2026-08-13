import Fuglede.Z180K18TerminalInterface

/-!
# Minimal exact boundary of the `m = 2` and `m = 4` branches

The external cardinality-eighteen audit first bounds all possible set-side
cyclotomic zero orders by an envelope and then enumerates every normalized
eighteen-clique in that envelope.  Only one consequence of the complete
profile tables is needed by the formal descent:

* no `m = 2` envelope clique has a difference of order ten;
* no `m = 4` envelope clique has a difference of order twenty.

But `Z180K18FiveFactorDefectAt m A L` contains an explicit pair of points of
`L` whose difference has order `5 * m`.  Consequently envelope completeness
plus these two tiny census consequences already contradict the defect.  The
four Fourier-cover routes and their six association-scheme forced zeros are
valid conditional endpoints, formalized separately in
`Z180K18LowOrderCovers`, but they are not needed for the actual terminal
branches once the distinguished defect edge is retained.

This file does not assert the two envelope computations or the two finite
clique censuses.  It exposes exactly those four facts as a `Prop` structure
and proves all remaining logical glue.
-/

namespace Fuglede

open Polynomial

/-- Every nonzero difference of `L` has an order in `orders`. -/
def Z180K18DifferenceOrderEnvelope
    (L : Finset (ZMod 180)) (orders : Finset Nat) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x ≠ y → frequencyOrder 180 (x - y) ∈ orders

/-- Every nontrivial divisor order at which the mask vanishes belongs to the
recorded finite envelope.  This is the direct semantic output of the 34
envelope-exclusion computations. -/
def Z180K18MaskZeroOrderEnvelope
    (A : Finset (ZMod 180)) (orders : Finset Nat) : Prop :=
  ∀ q : Nat, q ∣ 180 → 1 < q →
    (cyclotomic q Int ∣ maskPolynomial 180 A) → q ∈ orders

/-- Exact zero-order envelope used by the `m = 2` clique census. -/
def z180K18M2EnvelopeOrders : Finset Nat :=
  {3, 4, 9, 10, 12, 20, 36, 60, 180}

/-- Exact zero-order envelope used by the `m = 4` clique census. -/
def z180K18M4EnvelopeOrders : Finset Nat :=
  {2, 3, 6, 9, 10, 18, 20, 30, 45, 90}

/-- Semantic completeness statement for the `m = 2` zero-order envelope. -/
def Z180K18M2EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 2 A L →
    Z180K18MaskZeroOrderEnvelope A z180K18M2EnvelopeOrders

/-- Semantic completeness statement for the `m = 4` zero-order envelope. -/
def Z180K18M4EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 4 A L →
    Z180K18MaskZeroOrderEnvelope A z180K18M4EnvelopeOrders

/-- Minimal consequence of the complete ten-clique/two-profile `m = 2`
census: none of the ten normalized cliques has an order-ten edge. -/
def Z180K18M2NoHighEdgeCensusInterface : Prop :=
  ∀ L : Finset (ZMod 180),
    L.card = 18 →
    Z180K18DifferenceOrderEnvelope L z180K18M2EnvelopeOrders →
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 180 (x - y) ≠ 10

/-- Minimal consequence of the complete 3,125-clique/eleven-profile `m = 4`
census: none of the normalized cliques has an order-twenty edge. -/
def Z180K18M4NoHighEdgeCensusInterface : Prop :=
  ∀ L : Finset (ZMod 180),
    L.card = 18 →
    Z180K18DifferenceOrderEnvelope L z180K18M4EnvelopeOrders →
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 180 (x - y) ≠ 20

/-- The exact four-item boundary left by the low-order audit.  No inhabitant
is introduced in this module. -/
structure Z180K18LowOrderAuditInterface : Prop where
  m2Envelope : Z180K18M2EnvelopeInterface
  m4Envelope : Z180K18M4EnvelopeInterface
  m2NoHighEdge : Z180K18M2NoHighEdgeCensusInterface
  m4NoHighEdge : Z180K18M4NoHighEdgeCensusInterface

/-- Spectral differences turn a set-side mask-zero envelope into the matching
difference-order envelope on its spectrum. -/
theorem z180_k18_differenceOrderEnvelope_of_maskZeroOrderEnvelope
    {A L : Finset (ZMod 180)} {orders : Finset Nat}
    (hSpec : CyclotomicSpectrum 180 A L)
    (henvelope : Z180K18MaskZeroOrderEnvelope A orders) :
    Z180K18DifferenceOrderEnvelope L orders := by
  intro x hx y hy hne
  let q := frequencyOrder 180 (x - y)
  have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hqdiv : q ∣ 180 := frequencyOrder_dvd_modulus (x - y)
  have hqgt : 1 < q :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hdiff
  have hzero : CyclotomicZero 180 A (x - y) :=
    hSpec.2.2 x hx y hy hne
  apply henvelope q hqdiv hqgt
  simpa [CyclotomicZero, q] using hzero

/-- Envelope completeness and the order-ten-free clique census contradict
an `m = 2` defect, because the defect itself supplies an order-ten edge. -/
theorem z180_k18_no_m2_defect_of_lowOrderAudit
    (haudit : Z180K18LowOrderAuditInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 2 A L) : False := by
  have hcardL : L.card = 18 := hSpec.2.1.symm.trans hcard
  have hmaskEnv := haudit.m2Envelope A L hSpec hcard hcore hdefect
  have henv :=
    z180_k18_differenceOrderEnvelope_of_maskZeroOrderEnvelope hSpec hmaskEnv
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have havoid := haudit.m2NoHighEdge L hcardL henv l₁ hl₁ l₂ hl₂ hne
  apply havoid
  simpa using horder

/-- Envelope completeness and the order-twenty-free clique census contradict
an `m = 4` defect, because the defect itself supplies an order-twenty edge. -/
theorem z180_k18_no_m4_defect_of_lowOrderAudit
    (haudit : Z180K18LowOrderAuditInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 4 A L) : False := by
  have hcardL : L.card = 18 := hSpec.2.1.symm.trans hcard
  have hmaskEnv := haudit.m4Envelope A L hSpec hcard hcore hdefect
  have henv :=
    z180_k18_differenceOrderEnvelope_of_maskZeroOrderEnvelope hSpec hmaskEnv
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have havoid := haudit.m4NoHighEdge L hcardL henv l₁ hl₁ l₂ hl₂ hne
  apply havoid
  simpa using horder

/-- The four minimal low-order audit facts close both terminal branches. -/
theorem z180_k18_terminalBranches_two_four_of_lowOrderAudit
    (haudit : Z180K18LowOrderAuditInterface) :
    Z180K18TerminalBranchCertificate 2 ∧
      Z180K18TerminalBranchCertificate 4 := by
  constructor
  · intro A L hSpec hcard hcore hdefect
    exact False.elim
      (z180_k18_no_m2_defect_of_lowOrderAudit
        haudit hSpec hcard hcore hdefect)
  · intro A L hSpec hcard hcore hdefect
    exact False.elim
      (z180_k18_no_m4_defect_of_lowOrderAudit
        haudit hSpec hcard hcore hdefect)

#print axioms z180_k18_no_m2_defect_of_lowOrderAudit
#print axioms z180_k18_no_m4_defect_of_lowOrderAudit
#print axioms z180_k18_differenceOrderEnvelope_of_maskZeroOrderEnvelope
#print axioms z180_k18_terminalBranches_two_four_of_lowOrderAudit

end Fuglede
