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

/-- Core premise 0; source assertion 222; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : ((a 0 (axisSupportOfMask 2)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 1; source assertion 224; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : ((a 0 (axisSupportOfMask 4)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 2; source assertion 226; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : ((a 0 (axisSupportOfMask 8)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 3; source assertion 228; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : ((a 0 (axisSupportOfMask 16)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 4 (by decide)
  have hsupport : axisSupportOfMask 16 =
      ({4} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 4; source assertion 645; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (¬ (z 1 (axisSupportOfMask 2))) := by
  have hp := hconstraints.prime_exclusion 1 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 5; source assertion 647; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (¬ (z 1 (axisSupportOfMask 4))) := by
  have hp := hconstraints.prime_exclusion 1 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 6; source assertion 649; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (¬ (z 1 (axisSupportOfMask 8))) := by
  have hp := hconstraints.prime_exclusion 1 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 7; source assertion 698; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 6))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 4)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 4 =
          ({2} : AxisSupport2310) := by decide
      have hi' : i = 2 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (2 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 6 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 8; source assertion 700; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 10))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 10 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 9; source assertion 704; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 18))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 18 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 10; source assertion 721; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 12))) → (z 1 (axisSupportOfMask 4))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 4) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 4) =
            axisSupportOfMask 12 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 11; source assertion 725; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 20))) → (z 1 (axisSupportOfMask 4))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 4) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 4) =
            axisSupportOfMask 20 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 12; source assertion 740; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 14))) → (z 1 (axisSupportOfMask 6))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 6) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 6) =
            axisSupportOfMask 14 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 13; source assertion 742; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
    : (((z 1 (axisSupportOfMask 22))) → (z 1 (axisSupportOfMask 6))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 6) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 6) =
            axisSupportOfMask 22 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 14; source assertion 755; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
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

/-- Core premise 15; source assertion 772; family unchanged; normalized false. -/
theorem k2CollisionNormalizedCorePremise15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 2 a z)
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

/-- Core premise 0; source assertion 0; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : ((a 0 (axisSupportOfMask 0)) = 4) := by
  simpa [axisSupportOfMask] using hconstraints.diagonal 0

/-- Core premise 1; source assertion 97; family projection; normalized true. -/
theorem k4BaseNormalizedCorePremise1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((a 0 (axisSupportOfMask 0)) + (a 0 (axisSupportOfMask 2)) + (a 0 (axisSupportOfMask 4)) + (a 0 (axisSupportOfMask 6)) + (a 0 (axisSupportOfMask 8)) + (a 0 (axisSupportOfMask 10)) + (a 0 (axisSupportOfMask 12)) + (a 0 (axisSupportOfMask 14)) + (a 0 (axisSupportOfMask 16)) + (a 0 (axisSupportOfMask 18)) + (a 0 (axisSupportOfMask 20)) + (a 0 (axisSupportOfMask 22)) + (a 0 (axisSupportOfMask 24)) + (a 0 (axisSupportOfMask 26)) + (a 0 (axisSupportOfMask 28)) + (a 0 (axisSupportOfMask 30))) ≥ 8) := by
  have hprojection := hconstraints.projection_lower 0 (axisSupportOfMask 1)
  rw [balancedCollisionLower_axisSupportOfMask] at hprojection
  have hbound : balancedCollisionLower 4 (maskSupportModulus 1) = 8 := by decide
  rw [hbound] at hprojection
  rw [multiaxisProjectionCollision_aMask_row_1] at hprojection
  simp only [aMask_apply] at hprojection
  norm_num at hprojection ⊢
  linarith only [hprojection]

/-- Core premise 2; source assertion 222; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : ((a 0 (axisSupportOfMask 2)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 3; source assertion 224; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : ((a 0 (axisSupportOfMask 4)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 4; source assertion 226; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : ((a 0 (axisSupportOfMask 8)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 5; source assertion 228; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : ((a 0 (axisSupportOfMask 16)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 4 (by decide)
  have hsupport : axisSupportOfMask 16 =
      ({4} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 6; source assertion 629; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (¬ (z 1 (axisSupportOfMask 2))) := by
  have hp := hconstraints.prime_exclusion 1 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 7; source assertion 631; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (¬ (z 1 (axisSupportOfMask 4))) := by
  have hp := hconstraints.prime_exclusion 1 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 8; source assertion 633; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (¬ (z 1 (axisSupportOfMask 8))) := by
  have hp := hconstraints.prime_exclusion 1 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 9; source assertion 680; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 6))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 4)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 4 =
          ({2} : AxisSupport2310) := by decide
      have hi' : i = 2 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (2 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 6 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 10; source assertion 682; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 10))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 10 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 11; source assertion 686; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 18))) → (z 1 (axisSupportOfMask 2))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 2) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 2) =
            axisSupportOfMask 18 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 12; source assertion 702; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 12))) → (z 1 (axisSupportOfMask 4))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 4) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 4) =
            axisSupportOfMask 12 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 13; source assertion 706; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 20))) → (z 1 (axisSupportOfMask 4))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 4) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 4) =
            axisSupportOfMask 20 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 14; source assertion 720; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 14))) → (z 1 (axisSupportOfMask 6))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 6) (axisSupportOfMask 8)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 8 =
          ({3} : AxisSupport2310) := by decide
      have hi' : i = 3 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 6) =
            axisSupportOfMask 14 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 15; source assertion 722; family unchanged; normalized false. -/
theorem k4BaseNormalizedCorePremise15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 4 a z)
    : (((z 1 (axisSupportOfMask 22))) → (z 1 (axisSupportOfMask 6))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 6) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 6) =
            axisSupportOfMask 22 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

end Fuglede

-- END base-k4
