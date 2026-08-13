import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 1. -/

namespace Fuglede

/-- Core premise 10; source assertion 705. -/
theorem k1CollisionCompactShardedCorePremise10
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 5))) → (z 1 (axisSupportOfMask 1))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 1) (axisSupportOfMask 4)
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
      · have hmask : insert (2 : Fin 5) (axisSupportOfMask 1) =
            axisSupportOfMask 5 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 11; source assertion 707. -/
theorem k1CollisionCompactShardedCorePremise11
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 9))) → (z 1 (axisSupportOfMask 1))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 1) (axisSupportOfMask 8)
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
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 1) =
            axisSupportOfMask 9 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 12; source assertion 711. -/
theorem k1CollisionCompactShardedCorePremise12
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 17))) → (z 1 (axisSupportOfMask 1))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 1) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 1) =
            axisSupportOfMask 17 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 13; source assertion 720. -/
theorem k1CollisionCompactShardedCorePremise13
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 14; source assertion 722. -/
theorem k1CollisionCompactShardedCorePremise14
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 15; source assertion 726. -/
theorem k1CollisionCompactShardedCorePremise15
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 16; source assertion 734. -/
theorem k1CollisionCompactShardedCorePremise16
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 7))) → (z 1 (axisSupportOfMask 3))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 3) (axisSupportOfMask 4)
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
      · have hmask : insert (2 : Fin 5) (axisSupportOfMask 3) =
            axisSupportOfMask 7 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 17; source assertion 735. -/
theorem k1CollisionCompactShardedCorePremise17
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 11))) → (z 1 (axisSupportOfMask 3))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 3) (axisSupportOfMask 8)
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
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 3) =
            axisSupportOfMask 11 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 18; source assertion 737. -/
theorem k1CollisionCompactShardedCorePremise18
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 19))) → (z 1 (axisSupportOfMask 3))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 3) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 3) =
            axisSupportOfMask 19 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 19; source assertion 744. -/
theorem k1CollisionCompactShardedCorePremise19
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

end Fuglede
