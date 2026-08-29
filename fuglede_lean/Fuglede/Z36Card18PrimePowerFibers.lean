import Fuglede.Z36Card18PrimePowerFiberCore
import Fuglede.SpectralFourier
import Fuglede.PrimeLayerReduction
import Mathlib.Tactic

/-!
# Spectral cardinality eighteen implies tiling in `ZMod 36`

This is the `p = 2` instance of the prime-power fibre argument.  Mixing the
two possible nonzero orders in a projection-modulo-nine fibre would give the
dual spectrum simultaneous order-two and order-four zeros, contradicting
that its cardinality is eighteen.  The resulting uniform fibre order has an
explicit opposite-order two-point kernel complement.
-/

namespace Fuglede

/-- Exact proposition-valued interface for the cardinality-eighteen case. -/
def Z36SpectralCard18ImpliesTile : Prop :=
  ∀ A L : Finset (ZMod 36), A.card = 18 →
    CyclotomicSpectrum 36 A L →
      ∃ B : Finset (ZMod 36), Tiles A B

/-- The cardinality-eighteen argument produces the prime-layer fibre
certificate itself. -/
theorem z36_fiberOrderTilingCertificate_of_spectral_card_eighteen
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 18) :
    Nonempty (FiberOrderTilingCertificate A) := by
  by_cases htwo : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 9) = ZMod.cast a' ∧
      frequencyOrder 36 (a - a') = 2
  · have hAllTwo : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 9) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 2 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_two_or_four_of_cast9_eq
          a a' hne hcast with horder | horder
      · exact horder
      · rcases htwo with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual : CyclotomicSpectrum 36 L A :=
          cyclotomicSpectrum_dual hSpec
        have hzeroTwo : CyclotomicZero 36 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroFour : CyclotomicZero 36 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hdivL :=
          z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
            L huorder horder hzeroTwo hzeroFour
        have hcardL : L.card = 18 := by
          rw [← hSpec.2.1]
          exact hcard
        rw [hcardL] at hdivL
        omega
    refine ⟨{
      complement := z36Card18OrderFourComplement
      projectionModulus := 9
      setDifferenceOrder := 2
      complementDifferenceOrder := 4
      projectionModulus_dvd := by norm_num
      cardinality := by rw [hcard, z36Card18OrderFourComplement_card]
      complement_mem_kernel := by
        intro b hb
        exact z36Card18OrderFourComplement_cast9_zero hb
      set_fibre_order := hAllTwo
      complement_order := ?_
      orders_ne := by norm_num }⟩
    intro b hb b' hb' hne
    exact z36Card18OrderFourComplement_difference_order hb hb' hne
  · have hAllFour : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 9) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 4 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_two_or_four_of_cast9_eq
          a a' hne hcast with horder | horder
      · exact False.elim
          (htwo ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨{
      complement := z36Card18OrderTwoComplement
      projectionModulus := 9
      setDifferenceOrder := 4
      complementDifferenceOrder := 2
      projectionModulus_dvd := by norm_num
      cardinality := by rw [hcard, z36Card18OrderTwoComplement_card]
      complement_mem_kernel := by
        intro b hb
        exact z36Card18OrderTwoComplement_cast9_zero hb
      set_fibre_order := hAllFour
      complement_order := ?_
      orders_ne := by norm_num }⟩
    intro b hb b' hb' hne
    exact z36Card18OrderTwoComplement_difference_order hb hb' hne

/-- Cardinality eighteen inhabits the fibre branch of the general reduction
outcome. -/
theorem z36_primeLayerReductionOutcome_of_spectral_card_eighteen
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 18) :
    PrimeLayerReductionOutcome A L := by
  obtain ⟨certificate⟩ :=
    z36_fiberOrderTilingCertificate_of_spectral_card_eighteen hSpec hcard
  exact .fiber certificate

/-- Every cardinality-eighteen spectral subset of `ZMod 36` tiles. -/
theorem z36_exists_tiling_of_spectral_card_eighteen
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 18) :
    ∃ B : Finset (ZMod 36), Tiles A B := by
  by_cases htwo : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 9) = ZMod.cast a' ∧
      frequencyOrder 36 (a - a') = 2
  · have hAllTwo : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 9) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 2 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_two_or_four_of_cast9_eq
          a a' hne hcast with horder | horder
      · exact horder
      · rcases htwo with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual : CyclotomicSpectrum 36 L A :=
          cyclotomicSpectrum_dual hSpec
        have hzeroTwo : CyclotomicZero 36 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroFour : CyclotomicZero 36 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hdivL :=
          z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
            L huorder horder hzeroTwo hzeroFour
        have hcardL : L.card = 18 := by
          rw [← hSpec.2.1]
          exact hcard
        rw [hcardL] at hdivL
        omega
    refine ⟨z36Card18OrderFourComplement, ?_⟩
    apply tiles_of_cyclic_projection_fiber_opposite_orders
      (N := 36) (m := 9) (rA := 2) (rB := 4) (by norm_num)
    · rw [hcard, z36Card18OrderFourComplement_card]
    · intro b hb
      exact z36Card18OrderFourComplement_cast9_zero hb
    · exact hAllTwo
    · intro b hb b' hb' hne
      exact z36Card18OrderFourComplement_difference_order hb hb' hne
    · norm_num
  · have hAllFour : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 9) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 4 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_two_or_four_of_cast9_eq
          a a' hne hcast with horder | horder
      · exact False.elim
          (htwo ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨z36Card18OrderTwoComplement, ?_⟩
    apply tiles_of_cyclic_projection_fiber_opposite_orders
      (N := 36) (m := 9) (rA := 4) (rB := 2) (by norm_num)
    · rw [hcard, z36Card18OrderTwoComplement_card]
    · intro b hb
      exact z36Card18OrderTwoComplement_cast9_zero hb
    · exact hAllFour
    · intro b hb b' hb' hne
      exact z36Card18OrderTwoComplement_difference_order hb hb' hne
    · norm_num

/-- Proposition-valued endpoint used by subgroup induction. -/
theorem z36_spectral_card18_implies_tile :
    Z36SpectralCard18ImpliesTile := by
  intro A L hcard hSpec
  exact z36_exists_tiling_of_spectral_card_eighteen hSpec hcard

#print axioms z36_exists_tiling_of_spectral_card_eighteen
#print axioms z36_spectral_card18_implies_tile

end Fuglede
