import Fuglede.FourierCrossImplications
import Fuglede.ProjectionCollision
import Fuglede.PrimeSupport
import Fuglede.LabaMarshall

/-!
# The exact five-axis arithmetic relaxation

This module is the single Lean-side specification of the finite arithmetic
problem sent to the certificate checker.  A support is a subset of the five
CRT coordinates and a side is either the set (`0`) or its spectrum (`1`).

The definition deliberately names every family of constraints used by the
SMT generator: inner-distribution mass, parity and capacity, all projection
collision bounds, exact-support Fourier energies, the two spectral cross
implications, prime-support exclusions, and the Laba--Marshall multiprime
clause.  Certificate theorems should specialize this definition rather than
restate 235 unrelated conjunctions.
-/

namespace Fuglede

open scoped BigOperators
open Polynomial

/-- The 32 subsets of the five CRT axes. -/
abbrev AxisSupport2310 := Finset (Fin 5)

/-- Side `0` is the spectral set and side `1` is its spectrum. -/
abbrev SpectralPairSide := Fin 2

/-- Number of differences with any prescribed nonzero values on `D`.
This is `prod (p-1)` and is the valency of the corresponding relation in the
five-fold product association scheme. -/
def supportValency (D : AxisSupport2310) : Nat :=
  ∏ i ∈ D, (crt2310Modulus i - 1)

/-- The signed Krawtchouk transform of an abstract two-sided distribution. -/
noncomputable def multiaxisEnergy
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (D : AxisSupport2310) : Int :=
  ∑ T : AxisSupport2310, krawtchoukCoeff D T * a side T

/-- Collision count for projection onto the coordinates in `S`. -/
noncomputable def multiaxisProjectionCollision
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (S : AxisSupport2310) : Int :=
  ∑ T : AxisSupport2310, if Disjoint T S then a side T else 0

/-- Sharp balanced lower collision bound for `k` objects in `m` cells. -/
def balancedCollisionLower (k m : Nat) : Nat :=
  let u := k / m
  let r := k % m
  r * (u + 1) ^ 2 + (m - r) * u ^ 2

/-- Sharp capacity upper collision bound.  Each projection cell has
`2310 / m` points. -/
def projectionCapacityUpper (k m : Nat) : Nat :=
  capacityEnergy (2310 / m) k

/-- Exact inner distributions attached to a concrete ordered spectral pair. -/
noncomputable def spectralPairDistribution
    (A L : Finset (ZMod 2310)) :
    SpectralPairSide → AxisSupport2310 → Int :=
  fun side D ↦
    if side = 0 then innerDistributionInt A D
    else innerDistributionInt L D

/-- Exact energy-zero predicates attached to a concrete ordered spectral pair. -/
noncomputable def spectralPairEnergyZero
    (A L : Finset (ZMod 2310)) :
    SpectralPairSide → AxisSupport2310 → Prop :=
  fun side D ↦
    if side = 0 then supportEnergy A D = 0
    else supportEnergy L D = 0

/-- A canonical frequency having any prescribed exact CRT support. -/
noncomputable def canonicalSupportFrequency
    (D : AxisSupport2310) : CRT2310 :=
  fun i ↦ if i ∈ D then 1 else 0

@[simp] theorem crtVectorSupport_canonicalSupportFrequency
    (D : AxisSupport2310) :
    crtVectorSupport (canonicalSupportFrequency D) = D := by
  classical
  ext i
  have hi : 1 < crt2310Modulus i := by
    fin_cases i <;> norm_num [crt2310Modulus]
  letI : Fact (1 < crt2310Modulus i) := ⟨hi⟩
  simp [canonicalSupportFrequency, mem_crtVectorSupport]

theorem canonicalSupportFrequency_mem_exact
    (D : AxisSupport2310) :
    canonicalSupportFrequency D ∈ exactCRTFrequencies D := by
  exact mem_exactCRTFrequencies.mpr
    (crtVectorSupport_canonicalSupportFrequency D)

@[simp] theorem spectralPairDistribution_set
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    spectralPairDistribution A L 0 D = innerDistributionInt A D := by
  simp [spectralPairDistribution]

@[simp] theorem spectralPairDistribution_spectrum
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    spectralPairDistribution A L 1 D = innerDistributionInt L D := by
  simp [spectralPairDistribution]

@[simp] theorem spectralPairEnergyZero_set
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    spectralPairEnergyZero A L 0 D ↔ supportEnergy A D = 0 := by
  simp [spectralPairEnergyZero]

@[simp] theorem spectralPairEnergyZero_spectrum
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    spectralPairEnergyZero A L 1 D ↔ supportEnergy L D = 0 := by
  simp [spectralPairEnergyZero]

@[simp] theorem multiaxisEnergy_spectralPairDistribution_set
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    multiaxisEnergy (spectralPairDistribution A L) 0 D =
      supportEnergy A D := by
  simp [multiaxisEnergy, supportEnergy, spectralPairDistribution]

@[simp] theorem multiaxisEnergy_spectralPairDistribution_spectrum
    (A L : Finset (ZMod 2310)) (D : AxisSupport2310) :
    multiaxisEnergy (spectralPairDistribution A L) 1 D =
      supportEnergy L D := by
  simp [multiaxisEnergy, supportEnergy, spectralPairDistribution]

/-- A prime singleton energy cannot vanish unless that prime divides the
cardinality.  This packages the exact-support/Galois step used by each SMT
prime-exclusion assertion. -/
theorem supportEnergy_singleton_ne_zero_of_not_dvd
    (X : Finset (ZMod 2310)) (i : Fin 5)
    (hnot : ¬ crt2310Modulus i ∣ X.card) :
    supportEnergy X {i} ≠ 0 := by
  intro henergy
  have hall :=
    (supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310 X {i}).mp
      henergy
  let d : CRT2310 := canonicalSupportFrequency {i}
  have hd : d ∈ exactCRTFrequencies ({i} : AxisSupport2310) := by
    simpa [d] using canonicalSupportFrequency_mem_exact ({i} : AxisSupport2310)
  have hzero : CyclotomicZero 2310 X (fromCRT2310 d) := hall d hd
  have horder :
      frequencyOrder 2310 (fromCRT2310 d) = crt2310Modulus i := by
    rw [frequencyOrder_fromCRT2310_eq_supportModulus]
    have hs : crtVectorSupport d = ({i} : AxisSupport2310) :=
      mem_exactCRTFrequencies.mp hd
    rw [hs]
    simp [supportModulus]
  exact hnot (prime_dvd_card_of_cyclotomicZero
    (crt2310Modulus_prime i) X (fromCRT2310 d) horder hzero)

/-- Exact-support energy vanishing is precisely divisibility by the single
cyclotomic polynomial indexed by that CRT support. -/
theorem supportEnergy_eq_zero_iff_cyclotomic_support
    (X : Finset (ZMod 2310)) (D : AxisSupport2310) :
    supportEnergy X D = 0 ↔
      cyclotomic (supportModulus D) Int ∣ maskPolynomial 2310 X := by
  constructor
  · intro henergy
    have hall :=
      (supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310 X D).mp
        henergy
    let d : CRT2310 := canonicalSupportFrequency D
    have hd : d ∈ exactCRTFrequencies D := by
      simpa [d] using canonicalSupportFrequency_mem_exact D
    have hzero := hall d hd
    unfold CyclotomicZero at hzero
    rw [frequencyOrder_fromCRT2310_eq_supportModulus,
      mem_exactCRTFrequencies.mp hd] at hzero
    exact hzero
  · intro hdiv
    rw [supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310]
    intro d hd
    unfold CyclotomicZero
    rw [frequencyOrder_fromCRT2310_eq_supportModulus,
      mem_exactCRTFrequencies.mp hd]
    exact hdiv

/-- The exact necessary-condition system used by the multiaxis campaign.

The Boolean variables of the SMT files are represented by propositions
`z side D`; `zero_iff_energy` fixes them definitionally to the vanishing of
the corresponding integer Krawtchouk energy. -/
structure MultiaxisConstraints
    (k : Nat)
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (z : SpectralPairSide → AxisSupport2310 → Prop) : Prop where
  diagonal : ∀ side, a side ∅ = k
  nonnegative : ∀ side D, 0 ≤ a side D
  square_bound : ∀ side D, D ≠ ∅ → a side D ≤ (k ^ 2 : Nat)
  valency_bound : ∀ side D, D ≠ ∅ →
    a side D ≤ (k * supportValency D : Nat)
  even_off_diagonal : ∀ side D, D ≠ ∅ → Even (a side D)
  total_mass : ∀ side, (∑ D : AxisSupport2310, a side D) = (k ^ 2 : Nat)
  projection_lower : ∀ side S,
    (balancedCollisionLower k (supportModulus S) : Int) ≤
      multiaxisProjectionCollision a side S
  projection_upper : ∀ side S,
    multiaxisProjectionCollision a side S ≤
      (projectionCapacityUpper k (supportModulus S) : Int)
  energy_nonnegative : ∀ side D, D ≠ ∅ →
    0 ≤ multiaxisEnergy a side D
  zero_iff_energy : ∀ side D, D ≠ ∅ →
    (z side D ↔ multiaxisEnergy a side D = 0)
  zero_empty_false : ∀ side, ¬ z side ∅
  prime_exclusion : ∀ side i,
    ¬ crt2310Modulus i ∣ k →
      ¬ z side {i} ∧ a side {i} = 0
  laba_marshall : ∀ side base added,
    Disjoint base added →
    k < supportModulus added →
    (∀ i ∈ added, z side (insert i base)) →
    z side base
  cross_set_to_spectrum : ∀ D, D ≠ ∅ →
    0 < a 0 D → z 1 D
  cross_spectrum_to_set : ∀ D, D ≠ ∅ →
    0 < a 1 D → z 0 D

/-- The additional assertion used for a nontiling set at a divisor
cardinality: some nonempty difference is invisible to the selected
projection. -/
def HasProjectionCollision
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (S : AxisSupport2310) : Prop :=
  0 < ∑ T ∈ (Finset.univ : Finset AxisSupport2310).filter
      (fun T ↦ T ≠ ∅ ∧ Disjoint T S), a side T

/-- One exhaustive branch of a projection-collision disjunction. -/
def HasDifferenceSupport
    (a : SpectralPairSide → AxisSupport2310 → Int)
    (side : SpectralPairSide) (D : AxisSupport2310) : Prop :=
  0 < a side D

end Fuglede
