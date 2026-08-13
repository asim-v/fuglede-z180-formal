import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 6. -/

namespace Fuglede

/-- Core premise 60; source assertion 944. -/
theorem k1CollisionCompactShardedCorePremise60
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 31)) > 0) → (z 1 (axisSupportOfMask 31))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 31) (by decide) hpositive

/-- Core premise 61; source assertion 946. -/
theorem k1CollisionCompactShardedCorePremise61
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    (hcollision : HasProjectionCollision a 0 (axisSupportOfMask 0))
    : (((a 0 (axisSupportOfMask 1)) + (a 0 (axisSupportOfMask 2)) + (a 0 (axisSupportOfMask 3)) + (a 0 (axisSupportOfMask 4)) + (a 0 (axisSupportOfMask 5)) + (a 0 (axisSupportOfMask 6)) + (a 0 (axisSupportOfMask 7)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 9)) + (a 0 (axisSupportOfMask 10)) + (a 0 (axisSupportOfMask 11)) + (a 0 (axisSupportOfMask 12)) + (a 0 (axisSupportOfMask 13)) + (a 0 (axisSupportOfMask 14)) + (a 0 (axisSupportOfMask 15)) + (a 0 (axisSupportOfMask 16)) + (a 0 (axisSupportOfMask 17)) + (a 0 (axisSupportOfMask 18)) + (a 0 (axisSupportOfMask 19)) + (a 0 (axisSupportOfMask 20)) + (a 0 (axisSupportOfMask 21)) + (a 0 (axisSupportOfMask 22)) + (a 0 (axisSupportOfMask 23)) + (a 0 (axisSupportOfMask 24)) + (a 0 (axisSupportOfMask 25)) + (a 0 (axisSupportOfMask 26)) + (a 0 (axisSupportOfMask 27)) + (a 0 (axisSupportOfMask 28)) + (a 0 (axisSupportOfMask 29)) + (a 0 (axisSupportOfMask 30)) + (a 0 (axisSupportOfMask 31))) > 0) := by
  have hcollision' := hcollision
  unfold HasProjectionCollision at hcollision'
  have hfilter :
      (Finset.univ : Finset AxisSupport2310).filter
        (fun T => T ≠ ∅ ∧ Disjoint T (axisSupportOfMask 0)) =
        ({axisSupportOfMask 1, axisSupportOfMask 2, axisSupportOfMask 3, axisSupportOfMask 4, axisSupportOfMask 5, axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  rw [hfilter] at hcollision'
  have hnot_1 : axisSupportOfMask 1 ∉
      ({axisSupportOfMask 2, axisSupportOfMask 3, axisSupportOfMask 4, axisSupportOfMask 5, axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_2 : axisSupportOfMask 2 ∉
      ({axisSupportOfMask 3, axisSupportOfMask 4, axisSupportOfMask 5, axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_3 : axisSupportOfMask 3 ∉
      ({axisSupportOfMask 4, axisSupportOfMask 5, axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_4 : axisSupportOfMask 4 ∉
      ({axisSupportOfMask 5, axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_5 : axisSupportOfMask 5 ∉
      ({axisSupportOfMask 6, axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_6 : axisSupportOfMask 6 ∉
      ({axisSupportOfMask 7, axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_7 : axisSupportOfMask 7 ∉
      ({axisSupportOfMask 8, axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_8 : axisSupportOfMask 8 ∉
      ({axisSupportOfMask 9, axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_9 : axisSupportOfMask 9 ∉
      ({axisSupportOfMask 10, axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_10 : axisSupportOfMask 10 ∉
      ({axisSupportOfMask 11, axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_11 : axisSupportOfMask 11 ∉
      ({axisSupportOfMask 12, axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_12 : axisSupportOfMask 12 ∉
      ({axisSupportOfMask 13, axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_13 : axisSupportOfMask 13 ∉
      ({axisSupportOfMask 14, axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_14 : axisSupportOfMask 14 ∉
      ({axisSupportOfMask 15, axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_15 : axisSupportOfMask 15 ∉
      ({axisSupportOfMask 16, axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_16 : axisSupportOfMask 16 ∉
      ({axisSupportOfMask 17, axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_17 : axisSupportOfMask 17 ∉
      ({axisSupportOfMask 18, axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_18 : axisSupportOfMask 18 ∉
      ({axisSupportOfMask 19, axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_19 : axisSupportOfMask 19 ∉
      ({axisSupportOfMask 20, axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_20 : axisSupportOfMask 20 ∉
      ({axisSupportOfMask 21, axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_21 : axisSupportOfMask 21 ∉
      ({axisSupportOfMask 22, axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_22 : axisSupportOfMask 22 ∉
      ({axisSupportOfMask 23, axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_23 : axisSupportOfMask 23 ∉
      ({axisSupportOfMask 24, axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_24 : axisSupportOfMask 24 ∉
      ({axisSupportOfMask 25, axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_25 : axisSupportOfMask 25 ∉
      ({axisSupportOfMask 26, axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_26 : axisSupportOfMask 26 ∉
      ({axisSupportOfMask 27, axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_27 : axisSupportOfMask 27 ∉
      ({axisSupportOfMask 28, axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_28 : axisSupportOfMask 28 ∉
      ({axisSupportOfMask 29, axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_29 : axisSupportOfMask 29 ∉
      ({axisSupportOfMask 30, axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  have hnot_30 : axisSupportOfMask 30 ∉
      ({axisSupportOfMask 31} : Finset AxisSupport2310) := by
    decide
  rw [Finset.sum_insert hnot_1, Finset.sum_insert hnot_2, Finset.sum_insert hnot_3, Finset.sum_insert hnot_4, Finset.sum_insert hnot_5, Finset.sum_insert hnot_6, Finset.sum_insert hnot_7, Finset.sum_insert hnot_8, Finset.sum_insert hnot_9, Finset.sum_insert hnot_10, Finset.sum_insert hnot_11, Finset.sum_insert hnot_12, Finset.sum_insert hnot_13, Finset.sum_insert hnot_14, Finset.sum_insert hnot_15, Finset.sum_insert hnot_16, Finset.sum_insert hnot_17, Finset.sum_insert hnot_18, Finset.sum_insert hnot_19, Finset.sum_insert hnot_20, Finset.sum_insert hnot_21, Finset.sum_insert hnot_22, Finset.sum_insert hnot_23, Finset.sum_insert hnot_24, Finset.sum_insert hnot_25, Finset.sum_insert hnot_26, Finset.sum_insert hnot_27, Finset.sum_insert hnot_28, Finset.sum_insert hnot_29, Finset.sum_insert hnot_30, Finset.sum_singleton] at hcollision'
  simpa only [add_assoc] using hcollision'

end Fuglede
