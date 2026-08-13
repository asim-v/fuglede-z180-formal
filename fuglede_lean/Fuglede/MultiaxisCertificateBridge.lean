import Fuglede.MultiAxisBounds

/-!
# Typed interface for arithmetic UNSAT certificates

The imported solver proofs do not mention sets or Fourier analysis.  They
prove that no abstract functions `a,z` can satisfy the typed relaxation below.
These definitions are the narrow interface between those arithmetic theorems
and `Fuglede2310`.
-/

namespace Fuglede

open scoped BigOperators

/-- A base certificate excludes every abstract multiaxis solution of size
`k`; consequently no genuine spectral pair of that size can exist. -/
def BaseUnsatAt (k : Nat) : Prop :=
  ∀ (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop),
    MultiaxisConstraints k a z → False

/-- A collision certificate excludes a nontiling collision for the set side
under projection to `S`. -/
def CollisionUnsatAt (k : Nat) (S : AxisSupport2310) : Prop :=
  ∀ (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop),
    MultiaxisConstraints k a z → HasProjectionCollision a 0 S → False

/-- A branch certificate excludes one exact positive difference support. -/
def BranchUnsatAt (k : Nat) (side : SpectralPairSide)
    (D : AxisSupport2310) : Prop :=
  ∀ (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop),
    MultiaxisConstraints k a z → HasDifferenceSupport a side D → False

/-- Applying a base UNSAT theorem to the constraints realized by a spectral
pair gives an immediate contradiction. -/
theorem false_of_baseUnsatAt
    {k : Nat} (hcert : BaseUnsatAt k)
    {a : SpectralPairSide → AxisSupport2310 → Int}
    {z : SpectralPairSide → AxisSupport2310 → Prop}
    (hconstraints : MultiaxisConstraints k a z) : False :=
  hcert a z hconstraints

/-- Exhaustive positive-support branches imply the aggregated collision
certificate.  This is the formal coverage argument used for sizes
`55`, `77`, and `110`. -/
theorem collisionUnsatAt_of_branchUnsatAt
    {k : Nat} {S : AxisSupport2310}
    (hbranches : ∀ D, D ≠ ∅ → Disjoint D S →
      BranchUnsatAt k 0 D) :
    CollisionUnsatAt k S := by
  intro a z hconstraints hcollision
  unfold HasProjectionCollision at hcollision
  let supports := (Finset.univ : Finset AxisSupport2310).filter
    (fun D ↦ D ≠ ∅ ∧ Disjoint D S)
  have hnonnegative : ∀ D ∈ supports, 0 ≤ a 0 D := by
    intro D hD
    exact hconstraints.nonnegative 0 D
  have hexists : ∃ D ∈ supports, 0 < a 0 D :=
    (Finset.sum_pos_iff_of_nonneg hnonnegative).mp hcollision
  obtain ⟨D, hD, hpos⟩ := hexists
  have hsupport := (Finset.mem_filter.mp hD).2
  exact hbranches D hsupport.1 hsupport.2 a z hconstraints hpos

/-- Exact cast between the set-side collision sum used by certificates and
the natural-number inner-distribution sum used by the projection tiling
theorem. -/
theorem hasProjectionCollision_spectralPairDistribution_iff
    (A L : Finset (ZMod 2310)) (S : AxisSupport2310) :
    HasProjectionCollision (spectralPairDistribution A L) 0 S ↔
      0 < ∑ T ∈ (Finset.univ : Finset AxisSupport2310).filter
        (fun T ↦ T ≠ ∅ ∧ Disjoint T S), innerDistribution A T := by
  unfold HasProjectionCollision
  simp only [spectralPairDistribution_set, innerDistributionInt]
  norm_cast

/-- If the collision-augmented relaxation is UNSAT, the set is a complete
transversal and hence tiles by the kernel of the selected CRT projection. -/
theorem tiles_of_collisionUnsatAt
    {A L : Finset (ZMod 2310)} {S : AxisSupport2310}
    (hconstraints : MultiaxisConstraints A.card
      (spectralPairDistribution A L) (spectralPairEnergyZero A L))
    (hcert : CollisionUnsatAt A.card S)
    (hcard : A.card = Fintype.card (CRTProjection S)) :
    Tiles A (kernelFinset (crtProjection S)) := by
  have hnot :
      ¬ HasProjectionCollision (spectralPairDistribution A L) 0 S :=
    fun hcollision ↦ hcert _ _ hconstraints hcollision
  have hsum :
      (∑ T ∈ (Finset.univ : Finset AxisSupport2310).filter
        (fun T ↦ T ≠ ∅ ∧ Disjoint T S), innerDistribution A T) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hnot
      ((hasProjectionCollision_spectralPairDistribution_iff A L S).2 hpos)
  exact projection_tiles_kernel_of_sum_innerDistribution_eq_zero A S hsum hcard

/-- Cardinal-product spelling used for every divisor of `2310`. -/
theorem tiles_of_collisionUnsatAt_supportModulus
    {A L : Finset (ZMod 2310)} {S : AxisSupport2310}
    (hconstraints : MultiaxisConstraints A.card
      (spectralPairDistribution A L) (spectralPairEnergyZero A L))
    (hcert : CollisionUnsatAt A.card S)
    (hcard : A.card = supportModulus S) :
    Tiles A (kernelFinset (crtProjection S)) := by
  apply tiles_of_collisionUnsatAt hconstraints hcert
  rw [card_CRTProjection]
  exact hcard

end Fuglede
