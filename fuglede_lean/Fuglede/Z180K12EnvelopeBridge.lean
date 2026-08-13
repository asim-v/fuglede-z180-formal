import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180K12ForcedTypedAdapter
import Fuglede.Z180K12GraphKernel
import Fuglede.Z180Projection
import Mathlib.Tactic

/-!
# Exact interface from the cardinality-twelve sieve to the graph endpoint

This module separates the already kernel-checked implications from the two
finite/structural statements still represented by the exact enumeration:

* a non-tiler enters the normalized `m = 6` defect branch;
* every set in that branch has zero orders in `{2,4,10,30}`.

Given those explicitly named inputs, projection injectivity and the forced
order-two/order-four transform zeros are automatic, the exact safe envelope
embeds in the six-order graph envelope, and the kernel graph contradiction
closes the cardinality-twelve spectral branch.
-/

namespace Fuglede

open Polynomial

/-- Every fifth-coordinate level used by the exact `m = 6` enumeration is
nonempty. -/
def Z180K12FiveLevelsNonempty (A : Finset (ZMod 180)) : Prop :=
  ∀ r : ZMod 5, ∃ x ∈ A, (ZMod.cast x : ZMod 5) = r

/-- The surviving exact descent branch: `Phi_30` vanishes, `Phi_6` does not,
and all five coprime levels are nonempty. -/
def Z180K12M6Defect (A : Finset (ZMod 180)) : Prop :=
  cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
    ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A ∧
    Z180K12FiveLevelsNonempty A

/-- The smaller zero-order set produced by the exact integer sieve. -/
def Z180K12SafeDifference (d : ZMod 180) : Prop :=
  d ≠ 0 ∧
    (frequencyOrder 180 d = 2 ∨
     frequencyOrder 180 d = 4 ∨
     frequencyOrder 180 d = 10 ∨
     frequencyOrder 180 d = 30)

/-- Set-level form of the exact safe zero-order conclusion. -/
def Z180K12SafeZeroEnvelope (A : Finset (ZMod 180)) : Prop :=
  ∀ d : ZMod 180, d ≠ 0 → CyclotomicZero 180 A d →
    Z180K12SafeDifference d

/-- The exact m=6 zero-sieve statement, isolated as one formal interface.
The Python transcript with payload hash
`d3e848721aa27eba1bb63aa29af8fab9cc95b255be768d1fb08fbebaf16c7185`
is evidence for this proposition; it is not silently trusted here. -/
def Z180K12M6ExactZeroSieve : Prop :=
  ∀ A : Finset (ZMod 180),
    A.card = 12 →
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) →
    z180ExactOrderTransform A 2 = 0 →
    z180ExactOrderTransform A 4 = 0 →
    Z180K12M6Defect A →
    Z180K12SafeZeroEnvelope A

/-- The remaining descent statement: a putative non-tiler enters the unique
`m=6` branch left by the direct exact enumeration. -/
def Z180K12NonTilerM6Reduction (A : Finset (ZMod 180)) : Prop :=
  (¬ ∃ B : Finset (ZMod 180), Tiles A B) → Z180K12M6Defect A

/-- The exact four-order envelope is contained in the convenient six-order
compatibility envelope used by the graph theorem. -/
theorem z180_k12_safeDifference_implies_allowed (d : ZMod 180)
    (hsafe : Z180K12SafeDifference d) :
    Z180K12AllowedDifference d := by
  rcases hsafe with ⟨hne, horder⟩
  rcases horder with h2 | h4 | h10 | h30
  · exact ⟨hne, Or.inl h2⟩
  · exact ⟨hne, Or.inr (Or.inl h4)⟩
  · exact ⟨hne, Or.inr (Or.inr (Or.inr (Or.inl h10)))⟩
  · exact ⟨hne, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h30))))⟩

/-- Adapter from the exact enumeration result to the graph profile. -/
theorem z180_k12_safeZeroEnvelope_implies_graphProfile
    {A : Finset (ZMod 180)} (hsafe : Z180K12SafeZeroEnvelope A) :
    ∀ d : ZMod 180, d ≠ 0 →
      CyclotomicZero 180 A d → Z180K12AllowedDifference d := by
  intro d hne hzero
  exact z180_k12_safeDifference_implies_allowed d (hsafe d hne hzero)

/-- At cardinality twelve, projection to `ZMod 36` is injective on the set
side of every spectral pair. -/
theorem z180_k12_projection36_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) := by
  apply z180_projection36_injOn_of_spectral_not_five_dvd hSpec
  norm_num [hcard]

/-- Unconditional forced transform zeros, after discharging the Ramanujan
identities with their CRT proof. -/
theorem z180_k12_forced_transform_zeros_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12) :
    z180ExactOrderTransform A 2 = 0 ∧
      z180ExactOrderTransform A 4 = 0 ∧
      z180ExactOrderTransform L 2 = 0 ∧
      z180ExactOrderTransform L 4 = 0 := by
  exact z180_k12_forced_transform_zeros_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

/-- End-to-end conditional closure of the cardinality-twelve branch.  Its two
non-spectral inputs are precisely the descent-to-m6 statement and the exact
m6 zero sieve named above. -/
theorem z180_k12_exists_tiling_of_spectral_of_reduction_and_exactSieve
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12)
    (hreduction : Z180K12NonTilerM6Reduction A)
    (hsieve : Z180K12M6ExactZeroSieve) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_contra hnot
  have hinj := z180_k12_projection36_injOn_of_spectral hSpec hcard
  have hforced := z180_k12_forced_transform_zeros_of_spectral hSpec hcard
  have hsafe : Z180K12SafeZeroEnvelope A :=
    hsieve A hcard hinj hforced.1 hforced.2.1 (hreduction hnot)
  have hprofile := z180_k12_safeZeroEnvelope_implies_graphProfile hsafe
  have hcardL : L.card = 12 := by
    calc
      L.card = A.card := hSpec.2.1.symm
      _ = 12 := hcard
  exact z180_k12_no_twelve_point_spectrum_kernel
    A L hSpec hcardL hprofile

#print axioms z180_k12_safeDifference_implies_allowed
#print axioms z180_k12_projection36_injOn_of_spectral
#print axioms z180_k12_forced_transform_zeros_of_spectral
#print axioms z180_k12_exists_tiling_of_spectral_of_reduction_and_exactSieve

end Fuglede
