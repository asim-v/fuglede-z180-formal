import Fuglede.HighRangeBridge
import Fuglede.MultiaxisRealization
import Fuglede.MultiaxisCertificateBridge

/-!
# Fuglede at `2310` from complete certificate coverage

This file is the final abstract assembly point for the certificate campaign.
It deliberately does not enumerate the individual arithmetic certificates:
the sole hypothesis says that every possible proper spectral cardinality is
covered either by a base UNSAT certificate or by a projection-collision
UNSAT certificate at a CRT support of the same cardinality.
-/

namespace Fuglede

/-- The two possible certificate conclusions at one cardinality. -/
def CertificateAlternative2310 (k : Nat) : Prop :=
  BaseUnsatAt k ∨
    ∃ S : AxisSupport2310,
      k = supportModulus S ∧ CollisionUnsatAt k S

/-- Complete arithmetic-certificate coverage of every positive cardinality
allowed for a proper spectral subset of `ZMod 2310`. -/
def CertificateCoverage2310 : Prop :=
  ∀ k : Nat, 1 ≤ k → k ≤ 1155 →
    CertificateAlternative2310 k

/-- The low-range coverage represented by the 224 low/divisor artifacts:
185 base instances and 39 collision or collision-branch instances. -/
def LowCertificateCoverage2310 : Prop :=
  ∀ k : Nat, 1 ≤ k → k ≤ 210 →
    CertificateAlternative2310 k

/-- The eleven non-endpoint cardinalities left by the high-range structural
sieve. -/
def HighCoreCardinality2310 (k : Nat) : Prop :=
  k = 220 ∨ k = 231 ∨ k = 242 ∨ k = 253 ∨
  k = 264 ∨ k = 275 ∨ k = 286 ∨ k = 297 ∨
  k = 308 ∨ k = 319 ∨ k = 385

/-- Coverage represented by the eleven high-range certificate artifacts. -/
def HighCertificateCoverage2310 : Prop :=
  ∀ k : Nat, HighCoreCardinality2310 k →
    CertificateAlternative2310 k

private theorem exists_tile_of_certificateAlternative2310
    {A L : Finset (ZMod 2310)}
    (hconstraints : MultiaxisConstraints A.card
      (spectralPairDistribution A L) (spectralPairEnergyZero A L))
    (hcertificate : CertificateAlternative2310 A.card) :
    ∃ B : Finset (ZMod 2310), Tiles A B := by
  rcases hcertificate with hbase | ⟨S, hcard, hcollision⟩
  · exact False.elim (false_of_baseUnsatAt hbase hconstraints)
  · refine ⟨kernelFinset (crtProjection S), ?_⟩
    exact tiles_of_collisionUnsatAt_supportModulus
      hconstraints hcollision hcard

/-- Complete base-or-collision certificate coverage proves the spectral-to-
tiling direction of Fuglede's conjecture for `ZMod 2310`. -/
theorem fuglede2310_of_certificateCoverage
    (hcoverage : CertificateCoverage2310) : Fuglede2310 := by
  intro A L hSpec
  by_cases hproper : A ≠ Finset.univ
  · have hpos : 1 ≤ A.card := hSpec.1.card_pos
    have hle : A.card ≤ 1155 :=
      proper_cyclotomicSpectrum_card_le_1155 hSpec hproper
    have hconstraints :
        MultiaxisConstraints A.card
          (spectralPairDistribution A L) (spectralPairEnergyZero A L) :=
      cyclotomicSpectrum_yields_multiaxisConstraints hSpec
    exact exists_tile_of_certificateAlternative2310 hconstraints
      (hcoverage A.card hpos hle)
  · have hfull : A = Finset.univ := not_ne_iff.mp hproper
    subst A
    exact ⟨{0}, tiles_univ_singleton_zero⟩

/-- The exact 235-artifact assembly theorem.  The first hypothesis abstracts
the 224 low/divisor artifacts; the second abstracts precisely the eleven
high-range artifacts.  The four quotient-size high endpoints are discharged
structurally before the latter hypothesis is used. -/
theorem fuglede2310_of_campaignCertificateCoverage
    (hlow : LowCertificateCoverage2310)
    (hhigh : HighCertificateCoverage2310) : Fuglede2310 := by
  intro A L hSpec
  by_cases hproper : A ≠ Finset.univ
  · have hpos : 1 ≤ A.card := hSpec.1.card_pos
    have hconstraints :
        MultiaxisConstraints A.card
          (spectralPairDistribution A L) (spectralPairEnergyZero A L) :=
      cyclotomicSpectrum_yields_multiaxisConstraints hSpec
    by_cases hlowRange : A.card ≤ 210
    · exact exists_tile_of_certificateAlternative2310 hconstraints
        (hlow A.card hpos hlowRange)
    · have hlarge : 210 < A.card := Nat.lt_of_not_ge hlowRange
      rcases proper_spectral_high_cardinality_tiles_or_core_candidates
          hSpec hproper hlarge with htiles | hcore
      · exact htiles
      · have hcore' : HighCoreCardinality2310 A.card := hcore
        exact exists_tile_of_certificateAlternative2310 hconstraints
          (hhigh A.card hcore')
  · have hfull : A = Finset.univ := not_ne_iff.mp hproper
    subst A
    exact ⟨{0}, tiles_univ_singleton_zero⟩

end Fuglede
