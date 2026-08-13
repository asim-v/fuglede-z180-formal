import Fuglede.MultiaxisCertificateAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-! Opaque typed premises for pinned k=1 collision core shard 2. -/

namespace Fuglede

/-- Core premise 20; source assertion 748. -/
theorem k1CollisionCompactShardedCorePremise20
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 21; source assertion 757. -/
theorem k1CollisionCompactShardedCorePremise21
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 13))) → (z 1 (axisSupportOfMask 5))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 5) (axisSupportOfMask 8)
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
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 5) =
            axisSupportOfMask 13 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 22; source assertion 759. -/
theorem k1CollisionCompactShardedCorePremise22
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 21))) → (z 1 (axisSupportOfMask 5))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 5) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 5) =
            axisSupportOfMask 21 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 23; source assertion 764. -/
theorem k1CollisionCompactShardedCorePremise23
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 24; source assertion 766. -/
theorem k1CollisionCompactShardedCorePremise24
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 25; source assertion 770. -/
theorem k1CollisionCompactShardedCorePremise25
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 15))) → (z 1 (axisSupportOfMask 7))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 7) (axisSupportOfMask 8)
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
      · have hmask : insert (3 : Fin 5) (axisSupportOfMask 7) =
            axisSupportOfMask 15 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 26; source assertion 771. -/
theorem k1CollisionCompactShardedCorePremise26
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 23))) → (z 1 (axisSupportOfMask 7))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 7) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 7) =
            axisSupportOfMask 23 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 27; source assertion 780. -/
theorem k1CollisionCompactShardedCorePremise27
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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

/-- Core premise 28; source assertion 791. -/
theorem k1CollisionCompactShardedCorePremise28
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
    : (((z 1 (axisSupportOfMask 25))) → (z 1 (axisSupportOfMask 9))) := by
  intro hupper
  have hlaba := hconstraints.laba_marshall
    1 (axisSupportOfMask 9) (axisSupportOfMask 16)
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
      · have hmask : insert (4 : Fin 5) (axisSupportOfMask 9) =
            axisSupportOfMask 25 := by decide
        rw [hmask]
        exact hupper
    )
  exact hlaba

/-- Core premise 29; source assertion 798. -/
theorem k1CollisionCompactShardedCorePremise29
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop)
    (hconstraints : MultiaxisConstraints 1 a z)
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
