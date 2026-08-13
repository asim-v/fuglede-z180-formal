import Fuglede.Z180K18LowOrderInterfaces
import Fuglede.Z180K18M12DefectProfileAudit
import Fuglede.PrimeCyclotomic
import Fuglede.Z180DivisorCases
import Mathlib.Tactic

/-!
# Exact residual boundary for the three low-order (k = 18) envelopes

The full external audit excludes 24 nontrivial divisor orders from the
`m = 2,4,12` envelopes.  Six exclusions need no finite table:

* `q = m` contradicts the missing low factor stored in
  `Z180K18FiveFactorDefectAt m`;
* `q = 5` would force `5 ∣ A.card = 18`.

This module proves those six cases and reduces the three envelope interfaces
to exactly the remaining eighteen exclusions.  It does not introduce an
inhabitant for the residual interface.

The residual families and their canonical audit hashes are:

* `(m,q)=(2,6),(2,30)`: packed pair DP `(2,6)`,
  `ee1760e386a0f25a5d67e171f23edbf018d25623705089b11b00af765c062e3a`;
* `(2,18),(2,90)`: DP `(2,18)`,
  `1adfd507989a3eb9ca029fac7d75fde3f80c0f9793c1b3e832271e8d54c54b0a`;
* `(4,12),(4,60)`: DP `(4,12)`,
  `2657d268db2801b1bf503f29e01431570465d86da4bbe2773e6fc8eda023697d`;
* `(4,36),(4,180)`: DP `(4,36)`,
  `c694dd14aff21ca8bee76e8355ed87d9eb204dfba4af7a526235d599c32a8e86`;
* `(12,4),(12,20)`: DP `(12,4)`,
  `78d342bb89d751072a83b1ac199378cc51401c1f2dffe6341977bf1c1369c964`;
* `(12,6)`: DP `(12,6)`,
  `f603436c5c880a55b0895a32d4d3e575652187c58dfcd2e668759957d0c512e9`;
* `(12,18)`: DP `(12,18)`,
  `123ae99a7b12a72e11146675cf1401ec77e3d2a79014634f2d27981c61ca54f8`;
* `(12,36),(12,180)`: DP `(12,36)`,
  `168a2622a407534dda6e5d2f6320444a8d640653263751ece8beeeec29df4d77`;
* `(2,15),(2,45),(4,15)`: positive level-size arithmetic;
* `(12,45)`: 54-pattern table,
  `53e8e5dd757b2a7bfa3297af91b1da24bbb04445bc3a7d77722dbbd75db6aa30`.

Thus every still-open premise below names a genuine DP/table frontier.
-/

namespace Fuglede

open Polynomial

/-- The six non-elementary exclusions left in the `m = 2` branch. -/
def z180K18M2ResidualExcludedOrders : Finset Nat :=
  {6, 15, 18, 30, 45, 90}

/-- The five non-elementary exclusions left in the `m = 4` branch. -/
def z180K18M4ResidualExcludedOrders : Finset Nat :=
  {12, 15, 36, 60, 180}

/-- The seven non-elementary exclusions left in the `m = 12` branch. -/
def z180K18M12ResidualExcludedOrders : Finset Nat :=
  {4, 6, 18, 20, 36, 45, 180}

/-- Exact semantic output still needed from the `m = 2` DP/level audits. -/
def Z180K18M2ResidualEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 2 A L →
    ∀ q ∈ z180K18M2ResidualExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- Exact semantic output still needed from the `m = 4` DP/level audits. -/
def Z180K18M4ResidualEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 4 A L →
    ∀ q ∈ z180K18M4ResidualExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- Exact semantic output still needed from the `m = 12` DP/pattern audits. -/
def Z180K18M12ResidualEnvelopeInterface : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L →
    A.card = 18 →
    Z180K18CorePhi3Phi9Zeros A L →
    Z180K18FiveFactorDefectAt 12 A L →
    ∀ q ∈ z180K18M12ResidualExcludedOrders,
      ¬ cyclotomic q Int ∣ maskPolynomial 180 A

/-- The three genuine residual finite boundaries, with no hidden inhabitant. -/
structure Z180K18ResidualEnvelopeAuditInterface : Prop where
  m2 : Z180K18M2ResidualEnvelopeInterface
  m4 : Z180K18M4ResidualEnvelopeInterface
  m12 : Z180K18M12ResidualEnvelopeInterface

/-- Order five cannot be a zero of a cardinality-eighteen mask. -/
theorem z180_k18_not_cyclotomic_five_of_card
    {A : Finset (ZMod 180)} (hcard : A.card = 18) :
    ¬ cyclotomic 5 Int ∣ maskPolynomial 180 A := by
  intro hfive
  have hdiv : 5 ∣ A.card :=
    prime_dvd_card_of_cyclotomic_dvd_mask (by norm_num) A hfive
  rw [hcard] at hdiv
  norm_num at hdiv

/-- A defect at base order `m` already contains the negation of `Phi_m`. -/
theorem z180_k18_not_base_factor_of_fiveFactorDefect
    {m : Nat} {A L : Finset (ZMod 180)}
    (hdefect : Z180K18FiveFactorDefectAt m A L) :
    ¬ cyclotomic m Int ∣ maskPolynomial 180 A := by
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hbase, hhighOrder,
    hhigh, hnotlow⟩ := hdefect
  exact hnotlow

/-- The residual `m = 2` exclusions plus the two elementary lemmas inhabit
the full semantic envelope consumed by `Z180K18LowOrderInterfaces`. -/
theorem z180_k18_m2_envelope_of_residual
    (hres : Z180K18M2ResidualEnvelopeInterface) :
    Z180K18M2EnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect
  intro q hqdiv hqgt hqzero
  rcases dvd_180_cases (by omega) hqdiv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact False.elim
      ((z180_k18_not_base_factor_of_fiveFactorDefect hdefect) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]
  · norm_num [z180K18M2EnvelopeOrders]
  · exact False.elim
      ((z180_k18_not_cyclotomic_five_of_card hcard) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 6
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]
  · norm_num [z180K18M2EnvelopeOrders]
  · norm_num [z180K18M2EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 15
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 18
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 30
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 45
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 90
        (by norm_num [z180K18M2ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M2EnvelopeOrders]

/-- The corresponding exact assembly for the `m = 4` envelope. -/
theorem z180_k18_m4_envelope_of_residual
    (hres : Z180K18M4ResidualEnvelopeInterface) :
    Z180K18M4EnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect
  intro q hqdiv hqgt hqzero
  rcases dvd_180_cases (by omega) hqdiv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · norm_num [z180K18M4EnvelopeOrders]
  · norm_num [z180K18M4EnvelopeOrders]
  · exact False.elim
      ((z180_k18_not_base_factor_of_fiveFactorDefect hdefect) hqzero)
  · exact False.elim
      ((z180_k18_not_cyclotomic_five_of_card hcard) hqzero)
  · norm_num [z180K18M4EnvelopeOrders]
  · norm_num [z180K18M4EnvelopeOrders]
  · norm_num [z180K18M4EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 12
        (by norm_num [z180K18M4ResidualExcludedOrders])) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 15
        (by norm_num [z180K18M4ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M4EnvelopeOrders]
  · norm_num [z180K18M4EnvelopeOrders]
  · norm_num [z180K18M4EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 36
        (by norm_num [z180K18M4ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M4EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 60
        (by norm_num [z180K18M4ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M4EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 180
        (by norm_num [z180K18M4ResidualExcludedOrders])) hqzero)

/-- The corresponding exact assembly for the `m = 12` envelope. -/
theorem z180_k18_m12_envelope_of_residual
    (hres : Z180K18M12ResidualEnvelopeInterface) :
    Z180K18M12EnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect
  intro q hqdiv hqgt hqzero
  rcases dvd_180_cases (by omega) hqdiv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · norm_num [z180K18M12EnvelopeOrders]
  · norm_num [z180K18M12EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 4
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · exact False.elim
      ((z180_k18_not_cyclotomic_five_of_card hcard) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 6
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M12EnvelopeOrders]
  · norm_num [z180K18M12EnvelopeOrders]
  · exact False.elim
      ((z180_k18_not_base_factor_of_fiveFactorDefect hdefect) hqzero)
  · norm_num [z180K18M12EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 18
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 20
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M12EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 36
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 45
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)
  · norm_num [z180K18M12EnvelopeOrders]
  · norm_num [z180K18M12EnvelopeOrders]
  · exact False.elim
      ((hres A L hSpec hcard hcore hdefect 180
        (by norm_num [z180K18M12ResidualExcludedOrders])) hqzero)

/-- Packaging of the three full envelope interfaces after the honest residual
DP/table boundary has been supplied. -/
structure Z180K18EnvelopeInterfaces : Prop where
  m2 : Z180K18M2EnvelopeInterface
  m4 : Z180K18M4EnvelopeInterface
  m12 : Z180K18M12EnvelopeInterface

/-- No further mathematics is hidden between the residual exclusions and the
three envelope statements consumed by the terminal branches. -/
def z180K18EnvelopeInterfaces_of_residual
    (hres : Z180K18ResidualEnvelopeAuditInterface) :
    Z180K18EnvelopeInterfaces where
  m2 := z180_k18_m2_envelope_of_residual hres.m2
  m4 := z180_k18_m4_envelope_of_residual hres.m4
  m12 := z180_k18_m12_envelope_of_residual hres.m12

#print axioms z180_k18_not_cyclotomic_five_of_card
#print axioms z180_k18_not_base_factor_of_fiveFactorDefect
#print axioms z180_k18_m2_envelope_of_residual
#print axioms z180_k18_m4_envelope_of_residual
#print axioms z180_k18_m12_envelope_of_residual

end Fuglede
