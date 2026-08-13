import Fuglede.Z180K18M12ParityKernel

/-!
# Table-free root-parity kernel for the cardinality-eighteen `m = 12` branch

This module contains only the final algebraic part of the `m = 12` argument.
For one fifth-coordinate level, the three displayed equations are the
coefficient identities obtained from the proposed `Phi_12` root relation.
They force the selected eight phase counts to have odd total.  Applying that
fact to five levels contradicts a total selected mass of six.

No Fourier, fibre, or cyclotomic bridge is asserted here.  In particular, a
later semantic module must construct the phase-count records and prove the
total-mass hypothesis.
-/

namespace Fuglede

/-- The twelve integral phase multiplicities in one fifth-coordinate level,
together with the three coefficient identities used by the parity argument. -/
structure Z180K18M12PhaseCounts where
  count : Fin 12 -> Int
  h0 : count 0 - count 4 - count 6 + count 10 = 1
  h1 : count 1 - count 5 - count 7 + count 11 = 0
  h3 : count 3 + count 5 - count 9 - count 11 = 0

/-- The eight phase classes selected by the `m = 12` parity obstruction. -/
def z180K18M12SelectedPhaseCount (p : Z180K18M12PhaseCounts) : Int :=
  p.count 0 + p.count 1 + p.count 3 + p.count 4 +
    p.count 6 + p.count 7 + p.count 9 + p.count 10

/-- The three root-coefficient identities force the selected phase count in
one level to be odd. -/
theorem z180_k18_m12_level_selected_count_odd
    (p : Z180K18M12PhaseCounts) :
    ∃ k : Int, z180K18M12SelectedPhaseCount p = 2 * k + 1 := by
  refine ⟨p.count 4 + p.count 6 + p.count 7 + p.count 9, ?_⟩
  unfold z180K18M12SelectedPhaseCount
  linear_combination p.h0 + p.h1 + p.h3

/-- Five levels satisfying the root identities cannot have total selected
mass six.  This is the complete table-free arithmetic endpoint; it deliberately
does not construct the five records from spectral hypotheses. -/
theorem z180_k18_m12_five_level_root_parity_impossible
    (p : Fin 5 -> Z180K18M12PhaseCounts)
    (hsum :
      z180K18M12SelectedPhaseCount (p 0) +
        z180K18M12SelectedPhaseCount (p 1) +
        z180K18M12SelectedPhaseCount (p 2) +
        z180K18M12SelectedPhaseCount (p 3) +
        z180K18M12SelectedPhaseCount (p 4) = 6) :
    False := by
  rcases z180_k18_m12_level_selected_count_odd (p 0) with ⟨k0, hk0⟩
  rcases z180_k18_m12_level_selected_count_odd (p 1) with ⟨k1, hk1⟩
  rcases z180_k18_m12_level_selected_count_odd (p 2) with ⟨k2, hk2⟩
  rcases z180_k18_m12_level_selected_count_odd (p 3) with ⟨k3, hk3⟩
  rcases z180_k18_m12_level_selected_count_odd (p 4) with ⟨k4, hk4⟩
  exact z180_k18_m12_five_odd_sum_six_impossible
    (s0 := z180K18M12SelectedPhaseCount (p 0))
    (s1 := z180K18M12SelectedPhaseCount (p 1))
    (s2 := z180K18M12SelectedPhaseCount (p 2))
    (s3 := z180K18M12SelectedPhaseCount (p 3))
    (s4 := z180K18M12SelectedPhaseCount (p 4))
    (k0 := k0) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4)
    hsum hk0 hk1 hk2 hk3 hk4

#print axioms z180_k18_m12_level_selected_count_odd
#print axioms z180_k18_m12_five_level_root_parity_impossible

end Fuglede
