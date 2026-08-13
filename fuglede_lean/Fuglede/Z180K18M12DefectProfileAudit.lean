import Fuglede.Z180K18TerminalInterface
import Fuglede.Z180K18M12PairFibresExtraction
import Mathlib.Tactic

/-!
# Exact finite boundary for the `k = 18`, `m = 12` defect profile

The external audit has two logically separate outputs in this branch.

* On the set side, every possible nontrivial cyclotomic zero order of `A`
  lies in `{2,3,9,10,15,30,60,90}`.
* On the spectrum side, every cardinality-eighteen clique in that envelope
  has exact difference-order profile `{3,9,10,30,90}`.

The orientation matters.  The first statement concerns the mask of `A`.
Spectral orthogonality then turns `L` into the envelope clique.  Realized
orders `10`, `30`, and `90` in the difference profile of `L` force the three
corresponding cyclotomic factors on the mask of `A`, exactly as required by
`z180_k18_m12_pairFibres_of_cyclotomic_profile`.

There is also a shorter consequence which the longer phase argument does not
need: the exact profile contains no order `60`, whereas
`Z180K18FiveFactorDefectAt 12 A L` itself supplies an order-`60` difference
inside `L`.  Thus the same finite boundary already contradicts the defect.

This file introduces no inhabitant of either finite statement.  It packages
them as a two-field `Prop` interface and proves only the formal spectral and
logical assembly around that honest boundary.
-/

namespace Fuglede

open Polynomial

/-- The exact set-side zero-order envelope computed for the `m = 12` audit. -/
def z180K18M12EnvelopeOrders : Finset Nat :=
  {2, 3, 9, 10, 15, 30, 60, 90}

/-- The sole difference-order profile among the four normalized
cardinality-eighteen cliques in the `m = 12` envelope. -/
def z180K18M12ProfileOrders : Finset Nat :=
  {3, 9, 10, 30, 90}

/-- Every nontrivial divisor order at which the mask of `A` vanishes belongs
to the exact `m = 12` envelope. -/
def Z180K18M12MaskZeroEnvelope (A : Finset (ZMod 180)) : Prop :=
  ∀ q : Nat, q ∣ 180 → 1 < q →
    (cyclotomic q Int ∣ maskPolynomial 180 A) →
      q ∈ z180K18M12EnvelopeOrders

/-- Every nonzero difference of `L` has an order in the `m = 12` envelope. -/
def Z180K18M12DifferenceEnvelope (L : Finset (ZMod 180)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
    frequencyOrder 180 (x - y) ∈ z180K18M12EnvelopeOrders

/-- Exact semantic form of the sole `m = 12` clique profile: all nonzero
differences have one of the five displayed orders, and every displayed order
is realized by some difference. -/
def Z180K18M12ExactDifferenceProfile (L : Finset (ZMod 180)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 180 (x - y) ∈ z180K18M12ProfileOrders) ∧
    ∀ q ∈ z180K18M12ProfileOrders,
      ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧
        frequencyOrder 180 (x - y) = q

/-- Semantic completeness statement for the set-side `m = 12` envelope. -/
def Z180K18M12EnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 12 A L →
    Z180K18M12MaskZeroEnvelope A

/-- Exact finite census statement needed after envelope completeness.  The
external enumerator finds four normalized cliques, all with the one profile
recorded above; the count four is audit metadata and is not needed by the
formal descent. -/
def Z180K18M12CliqueCensusInterface : Prop :=
  ∀ L : Finset (ZMod 180),
    L.card = 18 →
    Z180K18M12DifferenceEnvelope L →
    Z180K18M12ExactDifferenceProfile L

/-- The exact two-item finite boundary left by the `m = 12` audit.  No
inhabitant is introduced in this module. -/
structure Z180K18M12DefectProfileAuditInterface : Prop where
  envelope : Z180K18M12EnvelopeInterface
  cliqueCensus : Z180K18M12CliqueCensusInterface

/-- Spectral differences turn the set-side mask-zero envelope into the
matching difference-order envelope on the spectrum. -/
theorem z180_k18_m12_differenceEnvelope_of_maskZeroEnvelope
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (henvelope : Z180K18M12MaskZeroEnvelope A) :
    Z180K18M12DifferenceEnvelope L := by
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

/-- Envelope completeness and the finite clique census give the unique exact
difference profile on `L`. -/
theorem z180_k18_m12_exactDifferenceProfile_of_audit
    (haudit : Z180K18M12DefectProfileAuditInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 12 A L) :
    Z180K18M12ExactDifferenceProfile L := by
  have hcardL : L.card = 18 := hSpec.2.1.symm.trans hcard
  have hmaskEnvelope := haudit.envelope A L hSpec hcard hcore hdefect
  have hdifferenceEnvelope :=
    z180_k18_m12_differenceEnvelope_of_maskZeroEnvelope hSpec hmaskEnvelope
  exact haudit.cliqueCensus L hcardL hdifferenceEnvelope

private theorem z180_k18_m12_factor_of_realized_spectral_order
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) {q : Nat}
    (hrealized :
      ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧
        frequencyOrder 180 (x - y) = q) :
    cyclotomic q Int ∣ maskPolynomial 180 A := by
  obtain ⟨x, hx, y, hy, hne, horder⟩ := hrealized
  have hzero : CyclotomicZero 180 A (x - y) :=
    hSpec.2.2 x hx y hy hne
  simpa [CyclotomicZero, horder] using hzero

/-- Correctly oriented bridge from the realized difference orders of `L` to
the three high cyclotomic factors of the mask of `A`. -/
theorem z180_k18_m12_highFactors_of_exactDifferenceProfile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hprofile : Z180K18M12ExactDifferenceProfile L) :
    (cyclotomic 10 Int ∣ maskPolynomial 180 A) ∧
      (cyclotomic 30 Int ∣ maskPolynomial 180 A) ∧
      (cyclotomic 90 Int ∣ maskPolynomial 180 A) := by
  have hrealized := hprofile.2
  constructor
  · apply z180_k18_m12_factor_of_realized_spectral_order hSpec
    exact hrealized 10 (by norm_num [z180K18M12ProfileOrders])
  · constructor
    · apply z180_k18_m12_factor_of_realized_spectral_order hSpec
      exact hrealized 30 (by norm_num [z180K18M12ProfileOrders])
    · apply z180_k18_m12_factor_of_realized_spectral_order hSpec
      exact hrealized 90 (by norm_num [z180K18M12ProfileOrders])

/-- The core factors and a correctly oriented exact profile supply all five
inputs of the unconditional pair-fibre extraction theorem. -/
theorem z180_k18_m12_pairFibres_of_exactDifferenceProfile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hprofile : Z180K18M12ExactDifferenceProfile L) :
    Nonempty (Z180K18M12PairFibres A) := by
  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have hfreq20 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60] using hcore.1
  have h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq20] using hcore.2.1
  obtain ⟨h10, h30, h90⟩ :=
    z180_k18_m12_highFactors_of_exactDifferenceProfile hSpec hprofile
  have hinj := z180_k18_projection36_injOn hSpec hcard
  exact z180_k18_m12_pairFibres_of_cyclotomic_profile
    hcard hinj h3 h9 h10 h30 h90

/-- The intended long route from the finite audit to pair fibres.  It is
recorded to expose the `A`/`L` orientation, although the next theorem shows
that the same hypotheses already contradict the defect. -/
theorem z180_k18_m12_pairFibres_of_defectProfileAudit
    (haudit : Z180K18M12DefectProfileAuditInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 12 A L) :
    Nonempty (Z180K18M12PairFibres A) := by
  apply z180_k18_m12_pairFibres_of_exactDifferenceProfile hSpec hcard hcore
  exact z180_k18_m12_exactDifferenceProfile_of_audit
    haudit hSpec hcard hcore hdefect

/-- The shorter terminal consequence: the defect supplies an order-`60`
edge of `L`, while the sole exact clique profile excludes order `60`. -/
theorem z180_k18_no_m12_defect_of_defectProfileAudit
    (haudit : Z180K18M12DefectProfileAuditInterface)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 12 A L) : False := by
  have hprofile := z180_k18_m12_exactDifferenceProfile_of_audit
    haudit hSpec hcard hcore hdefect
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have hmem := hprofile.1 l₁ hl₁ l₂ hl₂ hne
  have hsixty : (60 : Nat) ∈ z180K18M12ProfileOrders := by
    simpa [horder] using hmem
  norm_num [z180K18M12ProfileOrders] at hsixty

/-- Conditional terminal certificate obtained from the exact two-item finite
boundary.  Its conclusion is vacuous because the defect is contradictory. -/
theorem z180_k18_terminal_branch_twelve_of_defectProfileAudit
    (haudit : Z180K18M12DefectProfileAuditInterface) :
    Z180K18TerminalBranchCertificate 12 := by
  intro A L hSpec hcard hcore hdefect
  exact False.elim
    (z180_k18_no_m12_defect_of_defectProfileAudit
      haudit hSpec hcard hcore hdefect)

#print axioms z180_k18_m12_differenceEnvelope_of_maskZeroEnvelope
#print axioms z180_k18_m12_exactDifferenceProfile_of_audit
#print axioms z180_k18_m12_highFactors_of_exactDifferenceProfile
#print axioms z180_k18_m12_pairFibres_of_exactDifferenceProfile
#print axioms z180_k18_m12_pairFibres_of_defectProfileAudit
#print axioms z180_k18_no_m12_defect_of_defectProfileAudit
#print axioms z180_k18_terminal_branch_twelve_of_defectProfileAudit

end Fuglede
