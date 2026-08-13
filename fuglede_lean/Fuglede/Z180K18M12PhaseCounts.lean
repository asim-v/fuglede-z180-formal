import Fuglede.Z180K18M12PhaseFourierInterface

/-!
# Conditional assembly of the five normalized phase-count records

This module consumes exactly the analytic interface isolated in
`Z180K18M12PhaseFourierInterface`.  All other steps are kernel-level finite
combinatorics or integral polynomial algebra: choose a singleton pair level,
normalize by its phase, build the five `Z180K18M12PhaseCounts` records, and
show that their selected masses sum to six.
-/

namespace Fuglede

open Polynomial

/-- Five normalized phase-count records and their exact aggregate selected
mass, conditional only on the explicit Fourier cancellation interface. -/
theorem z180_k18_m12_phaseCounts_of_fourier_interface
    (hfourier : Z180K18M12PhaseFourierInterface)
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A) :
    ∃ q : Fin 5 → Z180K18M12PhaseCounts,
      z180K18M12SelectedPhaseCount (q 0) +
        z180K18M12SelectedPhaseCount (q 1) +
        z180K18M12SelectedPhaseCount (q 2) +
        z180K18M12SelectedPhaseCount (q 3) +
        z180K18M12SelectedPhaseCount (q 4) = 6 := by
  obtain ⟨c0, r0, hsingleton⟩ :=
    z180_k18_m12_exists_singleton_pairLevel_of_defect p h60 h12
  let shift : ZMod 12 := z180K18M12PairPhase p r0
  have hdiv : ∀ c : ZMod 5,
      cyclotomic 12 Int ∣
        z180K18M12NormalizedPhasePolynomial p shift c - 1 := by
    exact hfourier.normalized_level_phi12 A p c0 r0 hsingleton h60
  let q : Fin 5 → Z180K18M12PhaseCounts := fun c =>
    z180K18M12PhaseCounts_of_phi12_dvd p shift c (hdiv c)
  refine ⟨q, ?_⟩
  have hmass := z180_k18_m12_selected_phaseCounts_sum p shift
  have hexplicit := sum_zmod_five_explicit_phase (fun c : ZMod 5 =>
    z180K18M12NormalizedPhaseCount p shift c 0 +
      z180K18M12NormalizedPhaseCount p shift c 1 +
      z180K18M12NormalizedPhaseCount p shift c 3 +
      z180K18M12NormalizedPhaseCount p shift c 4 +
      z180K18M12NormalizedPhaseCount p shift c 6 +
      z180K18M12NormalizedPhaseCount p shift c 7 +
      z180K18M12NormalizedPhaseCount p shift c 9 +
      z180K18M12NormalizedPhaseCount p shift c 10)
  rw [hexplicit] at hmass
  norm_num [q, z180K18M12SelectedPhaseCount,
    z180K18M12PhaseCounts_of_phi12_dvd_count] at hmass ⊢
  exact hmass

/-- The complete table-free `m = 12` contradiction, with the single analytic
interface still visible as an explicit argument. -/
theorem z180_k18_m12_defect_impossible_of_fourier_interface
    (hfourier : Z180K18M12PhaseFourierInterface)
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A) :
    False := by
  obtain ⟨q, hsum⟩ :=
    z180_k18_m12_phaseCounts_of_fourier_interface hfourier p h60 h12
  exact z180_k18_m12_five_level_root_parity_impossible q hsum

#print axioms z180_k18_m12_phaseCounts_of_fourier_interface
#print axioms z180_k18_m12_defect_impossible_of_fourier_interface

end Fuglede
