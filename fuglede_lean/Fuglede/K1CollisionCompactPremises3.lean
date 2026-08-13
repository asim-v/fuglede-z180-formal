import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 3. -/

namespace Fuglede

/-- Core premise 30; source assertion 803. -/
theorem k1CollisionCompactShardedCorePremise30
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 27))) → (z 1 (axisSupportOfMask 11))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 11) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 11) =
            axisSupportOfMask 27 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 31; source assertion 808. -/
theorem k1CollisionCompactShardedCorePremise31
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 32; source assertion 813. -/
theorem k1CollisionCompactShardedCorePremise32
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 29))) → (z 1 (axisSupportOfMask 13))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 13) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 13) =
            axisSupportOfMask 29 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 33; source assertion 816. -/
theorem k1CollisionCompactShardedCorePremise33
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 34; source assertion 818. -/
theorem k1CollisionCompactShardedCorePremise34
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 31))) → (z 1 (axisSupportOfMask 15))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 15) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 15) =
            axisSupportOfMask 31 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 35; source assertion 888. -/
theorem k1CollisionCompactShardedCorePremise35
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 3)) > 0) → (z 1 (axisSupportOfMask 3))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 3) (by decide) hpositive

/-- Core premise 36; source assertion 892. -/
theorem k1CollisionCompactShardedCorePremise36
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 5)) > 0) → (z 1 (axisSupportOfMask 5))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 5) (by decide) hpositive

/-- Core premise 37; source assertion 894. -/
theorem k1CollisionCompactShardedCorePremise37
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 6)) > 0) → (z 1 (axisSupportOfMask 6))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 6) (by decide) hpositive

/-- Core premise 38; source assertion 896. -/
theorem k1CollisionCompactShardedCorePremise38
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 7)) > 0) → (z 1 (axisSupportOfMask 7))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 7) (by decide) hpositive

/-- Core premise 39; source assertion 900. -/
theorem k1CollisionCompactShardedCorePremise39
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((a 0 (axisSupportOfMask 9)) > 0) → (z 1 (axisSupportOfMask 9))) := by
  intro hpositive
  exact hconstraints.cross_set_to_spectrum (axisSupportOfMask 9) (by decide) hpositive

end Fuglede
