import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=242 core shard 2. -/

namespace Fuglede

/-- Core premise 20; source assertion 211. -/
theorem k242CorePremise20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((120 * (a 0 (axisSupportOfMask 0))) + ((-120) * (a 0 (axisSupportOfMask 1))) + ((-60) * (a 0 (axisSupportOfMask 2))) + (60 * (a 0 (axisSupportOfMask 3))) + (120 * (a 0 (axisSupportOfMask 4))) + ((-120) * (a 0 (axisSupportOfMask 5))) + ((-60) * (a 0 (axisSupportOfMask 6))) + (60 * (a 0 (axisSupportOfMask 7))) + ((-20) * (a 0 (axisSupportOfMask 8))) + (20 * (a 0 (axisSupportOfMask 9))) + (10 * (a 0 (axisSupportOfMask 10))) + ((-10) * (a 0 (axisSupportOfMask 11))) + ((-20) * (a 0 (axisSupportOfMask 12))) + (20 * (a 0 (axisSupportOfMask 13))) + (10 * (a 0 (axisSupportOfMask 14))) + ((-10) * (a 0 (axisSupportOfMask 15))) + ((-12) * (a 0 (axisSupportOfMask 16))) + (12 * (a 0 (axisSupportOfMask 17))) + (6 * (a 0 (axisSupportOfMask 18))) + ((-6) * (a 0 (axisSupportOfMask 19))) + ((-12) * (a 0 (axisSupportOfMask 20))) + (12 * (a 0 (axisSupportOfMask 21))) + (6 * (a 0 (axisSupportOfMask 22))) + ((-6) * (a 0 (axisSupportOfMask 23))) + (2 * (a 0 (axisSupportOfMask 24))) + ((-2) * (a 0 (axisSupportOfMask 25))) + ((-1) * (a 0 (axisSupportOfMask 26))) + (1 * (a 0 (axisSupportOfMask 27))) + (2 * (a 0 (axisSupportOfMask 28))) + ((-2) * (a 0 (axisSupportOfMask 29))) + ((-1) * (a 0 (axisSupportOfMask 30))) + (1 * (a 0 (axisSupportOfMask 31)))) ≥ 0) := by
  have henergy := hconstraints.energy_nonnegative 0 (axisSupportOfMask 27) (by decide)
  rw [multiaxisEnergy, sum_axisSupportOfMask_explicit] at henergy
  simp only [
    krawtchoukCoeff_axisSupportOfMask,
    maskKrawtchoukCoeff_27_0,
    maskKrawtchoukCoeff_27_1,
    maskKrawtchoukCoeff_27_2,
    maskKrawtchoukCoeff_27_3,
    maskKrawtchoukCoeff_27_4,
    maskKrawtchoukCoeff_27_5,
    maskKrawtchoukCoeff_27_6,
    maskKrawtchoukCoeff_27_7,
    maskKrawtchoukCoeff_27_8,
    maskKrawtchoukCoeff_27_9,
    maskKrawtchoukCoeff_27_10,
    maskKrawtchoukCoeff_27_11,
    maskKrawtchoukCoeff_27_12,
    maskKrawtchoukCoeff_27_13,
    maskKrawtchoukCoeff_27_14,
    maskKrawtchoukCoeff_27_15,
    maskKrawtchoukCoeff_27_16,
    maskKrawtchoukCoeff_27_17,
    maskKrawtchoukCoeff_27_18,
    maskKrawtchoukCoeff_27_19,
    maskKrawtchoukCoeff_27_20,
    maskKrawtchoukCoeff_27_21,
    maskKrawtchoukCoeff_27_22,
    maskKrawtchoukCoeff_27_23,
    maskKrawtchoukCoeff_27_24,
    maskKrawtchoukCoeff_27_25,
    maskKrawtchoukCoeff_27_26,
    maskKrawtchoukCoeff_27_27,
    maskKrawtchoukCoeff_27_28,
    maskKrawtchoukCoeff_27_29,
    maskKrawtchoukCoeff_27_30,
    maskKrawtchoukCoeff_27_31] at henergy
  norm_num at henergy ⊢
  linarith only [henergy]

/-- Core premise 21; source assertion 221. -/
theorem k242CorePremise21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (¬ (z 0 (axisSupportOfMask 2))) := by
  have hp := hconstraints.prime_exclusion 0 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 22; source assertion 222. -/
theorem k242CorePremise22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 0 (axisSupportOfMask 2)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 23; source assertion 224. -/
theorem k242CorePremise23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 0 (axisSupportOfMask 4)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 24; source assertion 225. -/
theorem k242CorePremise24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (¬ (z 0 (axisSupportOfMask 8))) := by
  have hp := hconstraints.prime_exclusion 0 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 25; source assertion 226. -/
theorem k242CorePremise25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 0 (axisSupportOfMask 8)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 26; source assertion 235. -/
theorem k242CorePremise26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((z 0 (axisSupportOfMask 6)) ∧ (z 0 (axisSupportOfMask 10)) ∧ (z 0 (axisSupportOfMask 18))) → (z 0 (axisSupportOfMask 2))) := by
  intro hupper
  apply hconstraints.laba_marshall
    0 (axisSupportOfMask 2) (axisSupportOfMask 28)
  · decide
  · decide
  · intro i hi
    have hadded : axisSupportOfMask 28 =
        ({2, 3, 4} : AxisSupport2310) := by decide
    have hi' : i = 2 ∨ i = 3 ∨ i = 4 := by
      rw [hadded] at hi
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
    rcases hi' with rfl | rfl | rfl
    · have hmask : insert (2 : Fin 5) (axisSupportOfMask 2) =
          axisSupportOfMask 6 := by decide
      rw [hmask]
      exact hupper.1
    · have hmask : insert (3 : Fin 5) (axisSupportOfMask 2) =
          axisSupportOfMask 10 := by decide
      rw [hmask]
      exact hupper.2.1
    · have hmask : insert (4 : Fin 5) (axisSupportOfMask 2) =
          axisSupportOfMask 18 := by decide
      rw [hmask]
      exact hupper.2.2

/-- Core premise 27; source assertion 239. -/
theorem k242CorePremise27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    (((z 0 (axisSupportOfMask 9)) ∧ (z 0 (axisSupportOfMask 10)) ∧ (z 0 (axisSupportOfMask 12)) ∧ (z 0 (axisSupportOfMask 24))) → (z 0 (axisSupportOfMask 8))) := by
  intro hupper
  apply hconstraints.laba_marshall
    0 (axisSupportOfMask 8) (axisSupportOfMask 23)
  · decide
  · decide
  · intro i hi
    have hadded : axisSupportOfMask 23 =
        ({0, 1, 2, 4} : AxisSupport2310) := by decide
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 := by
      rw [hadded] at hi
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
    rcases hi' with rfl | rfl | rfl | rfl
    · have hmask : insert (0 : Fin 5) (axisSupportOfMask 8) =
          axisSupportOfMask 9 := by decide
      rw [hmask]
      exact hupper.1
    · have hmask : insert (1 : Fin 5) (axisSupportOfMask 8) =
          axisSupportOfMask 10 := by decide
      rw [hmask]
      exact hupper.2.1
    · have hmask : insert (2 : Fin 5) (axisSupportOfMask 8) =
          axisSupportOfMask 12 := by decide
      rw [hmask]
      exact hupper.2.2.1
    · have hmask : insert (4 : Fin 5) (axisSupportOfMask 8) =
          axisSupportOfMask 24 := by decide
      rw [hmask]
      exact hupper.2.2.2

/-- Core premise 28; source assertion 240. -/
theorem k242CorePremise28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 0)) = 242) := by
  simpa [axisSupportOfMask] using hconstraints.diagonal 1

/-- Core premise 29; source assertion 247. -/
theorem k242CorePremise29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 242 a z) :
    ((a 1 (axisSupportOfMask 3)) ≥ 0) := by
  exact hconstraints.nonnegative 1 (axisSupportOfMask 3)

end Fuglede
