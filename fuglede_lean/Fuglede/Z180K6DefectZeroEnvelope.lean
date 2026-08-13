import Fuglede.Z180K6DefectZeroEnvelopeCore
import Fuglede.Z180K6HighOrderSemantic

/-!
# Unconditional zero-envelope assembly inside the cardinality-six defect branch

The high-order semantic adapters discharge the three parameters exposed by
`Z180K6DefectZeroEnvelopeCore`.  Consequently a spectral set of cardinality
six cannot satisfy a `Phi_30`/not-`Phi_6` defect: its full zero set would lie
in `{4, 30}`, contradicting the already checked terminal Cayley graph bound.

This theorem closes the *defect branch*.  It does not by itself assert that
every non-tiler enters that branch; that descent remains a separate theorem.
-/

namespace Fuglede

open Polynomial

/-- All three high orders dividing `36` are excluded in the defect branch.
The only use of spectrality here is to supply injectivity modulo `36` for the
order-`36` occupancy argument. -/
theorem z180_k6_defect_high_order_sieve
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    (¬ cyclotomic 12 Int ∣ maskPolynomial 180 X) ∧
      (¬ cyclotomic 18 Int ∣ maskPolynomial 180 X) ∧
      (¬ cyclotomic 36 Int ∣ maskPolynomial 180 X) := by
  refine ⟨
    z180_not_phi12_dvd_of_k6_phi30_defect X hcard h30 h6,
    z180_not_phi18_dvd_of_k6_phi30_defect X hcard h30 h6,
    ?_⟩
  exact z180_not_phi36_dvd_of_k6_phi30_defect X hcard
    (z180_k6_projection36_injOn_of_spectral hSpec hcard) h30 h6

/-- Every nonzero mask zero of a spectral cardinality-six defect has order
`4` or `30`. -/
theorem z180_k6_zeroEnvelope_of_phi30_defect
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    Z180K6ZeroEnvelope X := by
  obtain ⟨h12, h18, h36⟩ :=
    z180_k6_defect_high_order_sieve hSpec hcard h30 h6
  exact z180_k6_zeroEnvelope_of_phi30_defect_of_high_sieve
    hSpec hcard h30 h6 h12 h18 h36

/-- A cardinality-six spectral pair cannot inhabit the normalized defect
branch. -/
theorem z180_k6_phi30_defect_impossible_of_spectral
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) : False := by
  exact z180_k6_zeroEnvelope_impossible_of_spectral hSpec hcard
    (z180_k6_zeroEnvelope_of_phi30_defect hSpec hcard h30 h6)

#print axioms z180_k6_defect_high_order_sieve
#print axioms z180_k6_zeroEnvelope_of_phi30_defect
#print axioms z180_k6_phi30_defect_impossible_of_spectral

end Fuglede
