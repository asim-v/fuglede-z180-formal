import Fuglede.CompactMultiaxisNormalization

/-! Optional normalized typed-premise batch; provenance is per block. -/

-- BEGIN collision-k2-side0
-- Full SMT SHA-256: 97f31d7a9a4f118c56bd00f9788e1800d9bd96a906d412b777d1eae2ac28910e
-- Core-index SHA-256: af075d3fac182a018e898142cf7cb38ef39031281deaee13d7a29290e3912897
-- Normalizer source SHA-256: 74f1c4155904e8686e848ecb5d68c99fbf4972236a14c9a061cc9055b1045d23
-- Normalizer olean SHA-256: 6b50fc0106339149d8a6c48f40e0151332e86291eb186fa3262eafd444953086
-- Normalizer trust-check SHA-256: 57f2d5444006f179809973a94511c7430361015c4925fac58d31640ac01161e3
-- Normalizer independent-audit SHA-256: 414114dd0e5a7104d76f0d6b2b47642cec9d5a8718ecd117e3696af441f3eed6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned collision k=2.
Full SMT SHA-256: `97f31d7a9a4f118c56bd00f9788e1800d9bd96a906d412b777d1eae2ac28910e`.
Core-index SHA-256: `af075d3fac182a018e898142cf7cb38ef39031281deaee13d7a29290e3912897`.
Normalized premises: `true`.
Normalizer source SHA-256: `74f1c4155904e8686e848ecb5d68c99fbf4972236a14c9a061cc9055b1045d23`.
Normalizer olean SHA-256: `6b50fc0106339149d8a6c48f40e0151332e86291eb186fa3262eafd444953086`.
-/

namespace Fuglede

/-- Core premise 16; source assertion 781; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 28))) → (z 1 (axisSupportOfMask 12))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 12) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 12) =
            axisSupportOfMask 28 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 17; source assertion 788; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 30))) → (z 1 (axisSupportOfMask 14))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 14) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 14) =
            axisSupportOfMask 30 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 18; source assertion 858; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 6)) > 0) → (z 1 (axisSupportOfMask 6))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 6) (by decide) hpositive

/-- Core premise 19; source assertion 866; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 10)) > 0) → (z 1 (axisSupportOfMask 10))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 10) (by decide) hpositive

/-- Core premise 20; source assertion 870; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 12)) > 0) → (z 1 (axisSupportOfMask 12))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 12) (by decide) hpositive

/-- Core premise 21; source assertion 874; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 14)) > 0) → (z 1 (axisSupportOfMask 14))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 14) (by decide) hpositive

/-- Core premise 22; source assertion 882; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 18)) > 0) → (z 1 (axisSupportOfMask 18))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 18) (by decide) hpositive

/-- Core premise 23; source assertion 886; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 20)) > 0) → (z 1 (axisSupportOfMask 20))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 20) (by decide) hpositive

/-- Core premise 24; source assertion 890; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 22)) > 0) → (z 1 (axisSupportOfMask 22))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 22) (by decide) hpositive

/-- Core premise 25; source assertion 894; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 24)) > 0) → (z 1 (axisSupportOfMask 24))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 24) (by decide) hpositive

/-- Core premise 26; source assertion 898; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 26)) > 0) → (z 1 (axisSupportOfMask 26))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 26) (by decide) hpositive

/-- Core premise 27; source assertion 902; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 28)) > 0) → (z 1 (axisSupportOfMask 28))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 28) (by decide) hpositive

/-- Core premise 28; source assertion 906; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((a 0 (axisSupportOfMask 30)) > 0) → (z 1 (axisSupportOfMask 30))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 30) (by decide) hpositive

/-- Core premise 29; source assertion 910; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    (hcollision : HasProjectionCollision a 0 (axisSupportOfMask 1))
    : (((a 0 (axisSupportOfMask 2)) + (a 0 (axisSupportOfMask 4)) + (a 0 (axisSupportOfMask 6)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 10)) + (a 0 (axisSupportOfMask 12)) + (a 0 (axisSupportOfMask 14)) + (a 0 (axisSupportOfMask 16)) + (a 0 (axisSupportOfMask 18)) + (a 0 (axisSupportOfMask 20)) + (a 0 (axisSupportOfMask 22)) + (a 0 (axisSupportOfMask 24)) + (a 0 (axisSupportOfMask 26)) + (a 0 (axisSupportOfMask 28)) + (a 0 (axisSupportOfMask 30))) > 0) := by
  have hcollision' := hcollision
  unfold HasProjectionCollision at hcollision'
  have hfilter :
      (Finset.univ : Finset AxisSupport2310).filter
        (fun T => T ≠ ∅ ∧ Disjoint T (axisSupportOfMask 1)) =
        ({axisSupportOfMask 2, axisSupportOfMask 4, axisSupportOfMask 6, axisSupportOfMask 8, axisSupportOfMask 10, axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  rw [hfilter] at hcollision'
  have hnot_2 : axisSupportOfMask 2 ∉
      ({axisSupportOfMask 4, axisSupportOfMask 6, axisSupportOfMask 8, axisSupportOfMask 10, axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_4 : axisSupportOfMask 4 ∉
      ({axisSupportOfMask 6, axisSupportOfMask 8, axisSupportOfMask 10, axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_6 : axisSupportOfMask 6 ∉
      ({axisSupportOfMask 8, axisSupportOfMask 10, axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_8 : axisSupportOfMask 8 ∉
      ({axisSupportOfMask 10, axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_10 : axisSupportOfMask 10 ∉
      ({axisSupportOfMask 12, axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_12 : axisSupportOfMask 12 ∉
      ({axisSupportOfMask 14, axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_14 : axisSupportOfMask 14 ∉
      ({axisSupportOfMask 16, axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_16 : axisSupportOfMask 16 ∉
      ({axisSupportOfMask 18, axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_18 : axisSupportOfMask 18 ∉
      ({axisSupportOfMask 20, axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_20 : axisSupportOfMask 20 ∉
      ({axisSupportOfMask 22, axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_22 : axisSupportOfMask 22 ∉
      ({axisSupportOfMask 24, axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_24 : axisSupportOfMask 24 ∉
      ({axisSupportOfMask 26, axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_26 : axisSupportOfMask 26 ∉
      ({axisSupportOfMask 28, axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  have hnot_28 : axisSupportOfMask 28 ∉
      ({axisSupportOfMask 30} : Finset AxisSupport2310) := by
    decide
  rw [Finset.sum_insert hnot_2, Finset.sum_insert hnot_4, Finset.sum_insert hnot_6, Finset.sum_insert hnot_8, Finset.sum_insert hnot_10, Finset.sum_insert hnot_12, Finset.sum_insert hnot_14, Finset.sum_insert hnot_16, Finset.sum_insert hnot_18, Finset.sum_insert hnot_20, Finset.sum_insert hnot_22, Finset.sum_insert hnot_24, Finset.sum_insert hnot_26, Finset.sum_insert hnot_28, Finset.sum_singleton] at hcollision'
  simpa only [add_assoc] using hcollision'

end Fuglede

-- END collision-k2-side0

-- BEGIN base-k4
-- Full SMT SHA-256: 8047d44ede7ada27cde8eda3f81e9ee528a8d3a6b163088c537b915206df4978
-- Core-index SHA-256: 0d0e5142e7826cc5bd7f8ea35b6a4759fa0bc15ee5610668314b670537568502
-- Normalizer source SHA-256: 74f1c4155904e8686e848ecb5d68c99fbf4972236a14c9a061cc9055b1045d23
-- Normalizer olean SHA-256: 6b50fc0106339149d8a6c48f40e0151332e86291eb186fa3262eafd444953086
-- Normalizer trust-check SHA-256: 57f2d5444006f179809973a94511c7430361015c4925fac58d31640ac01161e3
-- Normalizer independent-audit SHA-256: 414114dd0e5a7104d76f0d6b2b47642cec9d5a8718ecd117e3696af441f3eed6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned base k=4.
Full SMT SHA-256: `8047d44ede7ada27cde8eda3f81e9ee528a8d3a6b163088c537b915206df4978`.
Core-index SHA-256: `0d0e5142e7826cc5bd7f8ea35b6a4759fa0bc15ee5610668314b670537568502`.
Normalized premises: `true`.
Normalizer source SHA-256: `74f1c4155904e8686e848ecb5d68c99fbf4972236a14c9a061cc9055b1045d23`.
Normalizer olean SHA-256: `6b50fc0106339149d8a6c48f40e0151332e86291eb186fa3262eafd444953086`.
-/

namespace Fuglede

/-- Core premise 16; source assertion 734; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 24))) → (z 1 (axisSupportOfMask 8))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 8) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 8) =
            axisSupportOfMask 24 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 17; source assertion 750; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 26))) → (z 1 (axisSupportOfMask 10))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 10) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 10) =
            axisSupportOfMask 26 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 18; source assertion 758; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 28))) → (z 1 (axisSupportOfMask 12))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 12) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 12) =
            axisSupportOfMask 28 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 19; source assertion 764; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 30))) → (z 1 (axisSupportOfMask 14))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 14) (axisSupportOfMask 16)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 16 =
          ({4} : AxisSupport2310) := by decide
      have hi' : i = 4 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 14) =
            axisSupportOfMask 30 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 20; source assertion 826; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 6)) > 0) → (z 1 (axisSupportOfMask 6))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 6) (by decide) hpositive

/-- Core premise 21; source assertion 834; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 10)) > 0) → (z 1 (axisSupportOfMask 10))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 10) (by decide) hpositive

/-- Core premise 22; source assertion 838; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 12)) > 0) → (z 1 (axisSupportOfMask 12))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 12) (by decide) hpositive

/-- Core premise 23; source assertion 842; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 14)) > 0) → (z 1 (axisSupportOfMask 14))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 14) (by decide) hpositive

/-- Core premise 24; source assertion 850; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 18)) > 0) → (z 1 (axisSupportOfMask 18))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 18) (by decide) hpositive

/-- Core premise 25; source assertion 854; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 20)) > 0) → (z 1 (axisSupportOfMask 20))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 20) (by decide) hpositive

/-- Core premise 26; source assertion 858; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 22)) > 0) → (z 1 (axisSupportOfMask 22))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 22) (by decide) hpositive

/-- Core premise 27; source assertion 862; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 24)) > 0) → (z 1 (axisSupportOfMask 24))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 24) (by decide) hpositive

/-- Core premise 28; source assertion 866; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 26)) > 0) → (z 1 (axisSupportOfMask 26))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 26) (by decide) hpositive

/-- Core premise 29; source assertion 870; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 28)) > 0) → (z 1 (axisSupportOfMask 28))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 28) (by decide) hpositive

/-- Core premise 30; source assertion 874; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise30
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 30)) > 0) → (z 1 (axisSupportOfMask 30))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 30) (by decide) hpositive

end Fuglede

-- END base-k4
