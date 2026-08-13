import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 0. -/

namespace Fuglede

/-- Core premise 0; source assertion 222. -/
theorem k1CollisionCompactShardedCorePremise0
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : ((a 0 (axisSupportOfMask 1)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 0 (by decide)
  have hsupport : axisSupportOfMask 1 =
      ({0} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 1; source assertion 224. -/
theorem k1CollisionCompactShardedCorePremise1
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : ((a 0 (axisSupportOfMask 2)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 2; source assertion 226. -/
theorem k1CollisionCompactShardedCorePremise2
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : ((a 0 (axisSupportOfMask 4)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 3; source assertion 228. -/
theorem k1CollisionCompactShardedCorePremise3
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : ((a 0 (axisSupportOfMask 8)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 4; source assertion 230. -/
theorem k1CollisionCompactShardedCorePremise4
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : ((a 0 (axisSupportOfMask 16)) = 0) := by
  have hp := hconstraints.prime_exclusion 0 4 (by decide)
  have hsupport : axisSupportOfMask 16 =
      ({4} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.2

/-- Core premise 5; source assertion 663. -/
theorem k1CollisionCompactShardedCorePremise5
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (¬ (z 1 (axisSupportOfMask 1))) := by
  have hp := hconstraints.prime_exclusion 1 0 (by decide)
  have hsupport : axisSupportOfMask 1 =
      ({0} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 6; source assertion 665. -/
theorem k1CollisionCompactShardedCorePremise6
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (¬ (z 1 (axisSupportOfMask 2))) := by
  have hp := hconstraints.prime_exclusion 1 1 (by decide)
  have hsupport : axisSupportOfMask 2 =
      ({1} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 7; source assertion 667. -/
theorem k1CollisionCompactShardedCorePremise7
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (¬ (z 1 (axisSupportOfMask 4))) := by
  have hp := hconstraints.prime_exclusion 1 2 (by decide)
  have hsupport : axisSupportOfMask 4 =
      ({2} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 8; source assertion 669. -/
theorem k1CollisionCompactShardedCorePremise8
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (¬ (z 1 (axisSupportOfMask 8))) := by
  have hp := hconstraints.prime_exclusion 1 3 (by decide)
  have hsupport : axisSupportOfMask 8 =
      ({3} : AxisSupport2310) := by decide
  rw [hsupport]
  exact hp.1

/-- Core premise 9; source assertion 704. -/
theorem k1CollisionCompactShardedCorePremise9
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 3))) → (z 1 (axisSupportOfMask 1))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 1) (axisSupportOfMask 2)
    (by decide)
    (by decide)
    (by
      intro i hi
      have hadded : axisSupportOfMask 2 =
          ({1} : AxisSupport2310) := by decide
      have hi' : i = 1 := by
        rw [hadded] at hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
      rcases hi' with rfl
      · have hmask : insert (1 : Fin 5) (axisSupportOfMask 1) =
            axisSupportOfMask 3 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

end Fuglede
