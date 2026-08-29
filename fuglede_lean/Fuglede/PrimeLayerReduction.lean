import Fuglede.CyclicCertificate
import Fuglede.ProjectionFiberTiling
import Fuglede.ProjectionLift

/-!
# Certificates for prime-layer reduction

This module declares the four structural outcomes used by the proposed
prime-layer rigidity principle.  It does not assert that every spectral pair
has one of these certificates.  Instead it fixes small, kernel-checkable
interfaces for:

* a complete transversal of a finite projection;
* spectral descent to a smaller cyclic quotient; and
* direct fibre closure by one exact difference order on each side; and
* direct fibre closure by two finite, disjoint palettes of exact orders.

The missing general theorem is the rigidity disjunction producing one of
these certificates from spectrality.
-/

namespace Fuglede

noncomputable section

variable {N M : Nat} [NeZero N] [NeZero M]

/-- Data proving that `A` is a complete collection of representatives for a
finite additive projection. -/
structure TransversalProjectionCertificate
    (A : Finset (ZMod N)) (φ : ZMod N →+ ZMod M) : Prop where
  difference_free :
    ∀ a ∈ A, ∀ b ∈ A, a - b ∈ φ.ker → a = b
  card_eq_codomain : A.card = Fintype.card (ZMod M)

/-- A transversal projection certificate closes the tiling goal directly. -/
theorem TransversalProjectionCertificate.tiles
    {A : Finset (ZMod N)} {φ : ZMod N →+ ZMod M}
    (certificate : TransversalProjectionCertificate A φ) :
    Tiles A (kernelFinset φ) :=
  transversal_tiles_kernel φ A certificate.difference_free
    certificate.card_eq_codomain

/-- Data for a genuine inductive descent.  Both sides project injectively and
their images remain a spectral pair in the smaller cyclic group. -/
structure SpectralQuotientDescentCertificate
    (A L : Finset (ZMod N)) (φ : ZMod N →+ ZMod M) : Prop where
  surjective : Function.Surjective φ
  set_injective : Set.InjOn φ (A : Set (ZMod N))
  spectrum_injective : Set.InjOn φ (L : Set (ZMod N))
  spectral_image : CyclotomicSpectrum M (A.image φ) (L.image φ)

/-- Fuglede in the quotient plus a spectral descent certificate gives a
tiling upstairs. -/
theorem SpectralQuotientDescentCertificate.tiles
    {A L : Finset (ZMod N)} {φ : ZMod N →+ ZMod M}
    (quotientFuglede : SpectralImpliesTileAt M)
    (certificate : SpectralQuotientDescentCertificate A L φ) :
    ∃ B : Finset (ZMod N), Tiles A B := by
  obtain ⟨C, hC⟩ := quotientFuglede (A.image φ) (L.image φ)
    certificate.spectral_image
  exact ⟨preimageFinset φ C,
    lift_tiles_of_image φ A C certificate.set_injective hC⟩

/-- A direct prime-power fibre endpoint.  The complement lies in the kernel
of a cyclic projection, and nontrivial differences on the two factors have
distinct exact orders. -/
structure FiberOrderTilingCertificate
    (A : Finset (ZMod N)) where
  complement : Finset (ZMod N)
  projectionModulus : Nat
  setDifferenceOrder : Nat
  complementDifferenceOrder : Nat
  projectionModulus_dvd : projectionModulus ∣ N
  cardinality : A.card * complement.card = N
  complement_mem_kernel :
    ∀ b ∈ complement,
      (ZMod.cast b : ZMod projectionModulus) = 0
  set_fibre_order :
    ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      (ZMod.cast a : ZMod projectionModulus) = ZMod.cast a' →
      frequencyOrder N (a - a') = setDifferenceOrder
  complement_order :
    ∀ b ∈ complement, ∀ b' ∈ complement, b ≠ b' →
      frequencyOrder N (b - b') = complementDifferenceOrder
  orders_ne : setDifferenceOrder ≠ complementDifferenceOrder

/-- A fibre-order certificate closes the tiling goal directly. -/
theorem FiberOrderTilingCertificate.tiles
    {A : Finset (ZMod N)}
    (certificate : FiberOrderTilingCertificate A) :
    Tiles A certificate.complement :=
  tiles_of_cyclic_projection_fiber_opposite_orders
    certificate.projectionModulus_dvd
    certificate.cardinality
    certificate.complement_mem_kernel
    certificate.set_fibre_order
    certificate.complement_order
    certificate.orders_ne

/-- Direct fibre closure with finite, disjoint palettes of possible exact
difference orders.  This strictly generalizes `FiberOrderTilingCertificate`
and is the correct interface once a fibre or its complement is not
monochromatic in exact order. -/
structure FiberOrderPaletteTilingCertificate
    (A : Finset (ZMod N)) where
  complement : Finset (ZMod N)
  projectionModulus : Nat
  setDifferenceOrders : Finset Nat
  complementDifferenceOrders : Finset Nat
  projectionModulus_dvd : projectionModulus ∣ N
  cardinality : A.card * complement.card = N
  complement_mem_kernel :
    ∀ b ∈ complement,
      (ZMod.cast b : ZMod projectionModulus) = 0
  set_fibre_orders :
    ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      (ZMod.cast a : ZMod projectionModulus) = ZMod.cast a' →
      frequencyOrder N (a - a') ∈ setDifferenceOrders
  complement_orders :
    ∀ b ∈ complement, ∀ b' ∈ complement, b ≠ b' →
      frequencyOrder N (b - b') ∈ complementDifferenceOrders
  orders_disjoint :
    Disjoint setDifferenceOrders complementDifferenceOrders

/-- Disjoint order palettes close the tiling goal directly. -/
theorem FiberOrderPaletteTilingCertificate.tiles
    {A : Finset (ZMod N)}
    (certificate : FiberOrderPaletteTilingCertificate A) :
    Tiles A certificate.complement :=
  tiles_of_cyclic_projection_fiber_disjoint_order_palettes
    certificate.projectionModulus_dvd
    certificate.cardinality
    certificate.complement_mem_kernel
    certificate.set_fibre_orders
    certificate.complement_orders
    certificate.orders_disjoint

/-! ## The rigidity disjunction and its inductive assembly -/

/-- The four admissible outcomes of one prime-layer reduction step.

The descent constructor records strict decrease of the modulus.  This is the
well-founded datum needed to turn a uniform rigidity theorem into an
induction over all cyclic groups. -/
inductive PrimeLayerReductionOutcome
    (A L : Finset (ZMod N)) : Prop where
  | transversal {M : Nat} [NeZero M]
      (φ : ZMod N →+ ZMod M)
      (certificate : TransversalProjectionCertificate A φ)
  | descent {M : Nat} [NeZero M]
      (proper : M < N)
      (φ : ZMod N →+ ZMod M)
      (certificate : SpectralQuotientDescentCertificate A L φ)
  | fiber (certificate : FiberOrderTilingCertificate A)
  | fiberPalette (certificate : FiberOrderPaletteTilingCertificate A)

/-- Every certified outcome closes the tiling goal, using the induction
hypothesis only in the strict quotient-descent branch. -/
theorem PrimeLayerReductionOutcome.tiles
    {A L : Finset (ZMod N)}
    (properFuglede :
      ∀ (M : Nat) [NeZero M], M < N → SpectralImpliesTileAt M)
    (outcome : PrimeLayerReductionOutcome A L) :
    ∃ B : Finset (ZMod N), Tiles A B := by
  cases outcome with
  | transversal φ certificate =>
      exact ⟨kernelFinset φ, certificate.tiles⟩
  | descent proper φ certificate =>
      exact certificate.tiles (properFuglede _ proper)
  | fiber certificate =>
      exact ⟨certificate.complement, certificate.tiles⟩
  | fiberPalette certificate =>
      exact ⟨certificate.complement, certificate.tiles⟩

/-- Prime-layer rigidity at `N` is precisely the missing assertion that
spectrality always produces one of the four checkable outcomes. -/
def PrimeLayerRigidityAt (N : Nat) [NeZero N] : Prop :=
  ∀ A L : Finset (ZMod N),
    CyclotomicSpectrum N A L → PrimeLayerReductionOutcome A L

/-- One rigidity step, together with Fuglede for every smaller modulus,
proves Fuglede at the current modulus. -/
theorem spectralImpliesTileAt_of_primeLayerRigidity
    (rigidity : PrimeLayerRigidityAt N)
    (properFuglede :
      ∀ (M : Nat) [NeZero M], M < N → SpectralImpliesTileAt M) :
    SpectralImpliesTileAt N := by
  intro A L hSpectrum
  exact (rigidity A L hSpectrum).tiles properFuglede

/-- A uniform proof of the rigidity disjunction implies the
spectral-to-tiling direction of Fuglede for every nonzero cyclic modulus. -/
theorem spectralImpliesTileAt_all_of_primeLayerRigidity
    (rigidity : ∀ (N : Nat) [NeZero N], PrimeLayerRigidityAt N) :
    ∀ (N : Nat) [NeZero N], SpectralImpliesTileAt N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N inductionHypothesis =>
      intro hN
      apply spectralImpliesTileAt_of_primeLayerRigidity (rigidity N)
      intro M hM hMN
      exact inductionHypothesis M hMN

end

end Fuglede
