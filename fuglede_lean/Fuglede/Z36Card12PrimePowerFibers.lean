import Fuglede.Z36Card12PrimePowerFiberCore
import Fuglede.Z36Card6ForcingThreeNine
import Fuglede.PrimeLayerReduction
import Mathlib.Tactic

/-!
# FKMS prime-power fibre theorem at cardinality twelve in `ZMod 36`

Here `36 / gcd 36 12 = 3`.  This is the `p^k` hypothesis of FKMS,
Proposition 4.2, specialized to `p = 3` and `k = 1`.  Projection modulo four
reduces the proof to the two possible nonzero orders in its nine-point
kernel.  Spectral duality and the prime-square cardinality obstruction rule
out mixing those orders; the opposite three-point kernel pattern then tiles.
-/

namespace Fuglede

/-- Exact smaller-modulus interface used by cardinality-twelve descent from
`ZMod 180`. -/
def Z36SpectralCard12ImpliesTile : Prop :=
  ∀ A L : Finset (ZMod 36), A.card = 12 →
    CyclotomicSpectrum 36 A L →
      ∃ B : Finset (ZMod 36), Tiles A B

/-- The cardinality-twelve argument produces the actual prime-layer fibre
certificate, not merely its tiling consequence. -/
theorem z36_fiberOrderTilingCertificate_of_spectral_card_twelve
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 12) :
    Nonempty (FiberOrderTilingCertificate A) := by
  by_cases hthree : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 4) = ZMod.cast a' ∧
      frequencyOrder 36 (a - a') = 3
  · have hAllThree : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 4) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 3 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_three_or_nine_of_cast4_eq
          a a' hne hcast with horder | horder
      · exact horder
      · rcases hthree with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual : CyclotomicSpectrum 36 L A :=
          cyclotomicSpectrum_dual hSpec
        have hzeroThreeRaw : CyclotomicZero 36 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroNineRaw : CyclotomicZero 36 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hzeroThree : Z36ZeroAtOrder L 3 := by
          simpa [CyclotomicZero, Z36ZeroAtOrder, huorder] using hzeroThreeRaw
        have hzeroNine : Z36ZeroAtOrder L 9 := by
          simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using hzeroNineRaw
        have hdivL :=
          z36_nine_dvd_card_of_zeros_three_and_nine
            L hzeroThree hzeroNine
        have hcardL : L.card = 12 := by
          rw [← hSpec.2.1]
          exact hcard
        rw [hcardL] at hdivL
        omega
    refine ⟨{
      complement := z36OrderNineComplement
      projectionModulus := 4
      setDifferenceOrder := 3
      complementDifferenceOrder := 9
      projectionModulus_dvd := by norm_num
      cardinality := by rw [hcard, z36OrderNineComplement_card]
      complement_mem_kernel := by
        intro b hb
        exact z36OrderNineComplement_cast4_zero hb
      set_fibre_order := hAllThree
      complement_order := ?_
      orders_ne := by norm_num }⟩
    intro b hb b' hb' hne
    exact z36OrderNineComplement_difference_order hb hb' hne
  · have hAllNine : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 4) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 9 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_three_or_nine_of_cast4_eq
          a a' hne hcast with horder | horder
      · exact False.elim
          (hthree ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨{
      complement := z36OrderThreeComplement
      projectionModulus := 4
      setDifferenceOrder := 9
      complementDifferenceOrder := 3
      projectionModulus_dvd := by norm_num
      cardinality := by rw [hcard, z36OrderThreeComplement_card]
      complement_mem_kernel := by
        intro b hb
        exact z36OrderThreeComplement_cast4_zero hb
      set_fibre_order := hAllNine
      complement_order := ?_
      orders_ne := by norm_num }⟩
    intro b hb b' hb' hne
    exact z36OrderThreeComplement_difference_order hb hb' hne

/-- Cardinality twelve inhabits the fibre branch of the general reduction
outcome. -/
theorem z36_primeLayerReductionOutcome_of_spectral_card_twelve
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 12) :
    PrimeLayerReductionOutcome A L := by
  obtain ⟨certificate⟩ :=
    z36_fiberOrderTilingCertificate_of_spectral_card_twelve hSpec hcard
  exact .fiber certificate

/-- Every cardinality-twelve spectral set in `ZMod 36` tiles. -/
theorem z36_exists_tiling_of_spectral_card_twelve
    {A L : Finset (ZMod 36)}
    (hSpec : CyclotomicSpectrum 36 A L) (hcard : A.card = 12) :
    ∃ B : Finset (ZMod 36), Tiles A B := by
  by_cases hthree : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 4) = ZMod.cast a' ∧
      frequencyOrder 36 (a - a') = 3
  · have hAllThree : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 4) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 3 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_three_or_nine_of_cast4_eq
          a a' hne hcast with horder | horder
      · exact horder
      · rcases hthree with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual : CyclotomicSpectrum 36 L A :=
          cyclotomicSpectrum_dual hSpec
        have hzeroThreeRaw : CyclotomicZero 36 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroNineRaw : CyclotomicZero 36 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hzeroThree : Z36ZeroAtOrder L 3 := by
          simpa [CyclotomicZero, Z36ZeroAtOrder, huorder] using hzeroThreeRaw
        have hzeroNine : Z36ZeroAtOrder L 9 := by
          simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using hzeroNineRaw
        have hdivL :=
          z36_nine_dvd_card_of_zeros_three_and_nine
            L hzeroThree hzeroNine
        have hcardL : L.card = 12 := by
          rw [← hSpec.2.1]
          exact hcard
        rw [hcardL] at hdivL
        omega
    refine ⟨z36OrderNineComplement, ?_⟩
    apply tiles_of_cyclic_projection_fiber_opposite_orders
      (N := 36) (m := 4) (rA := 3) (rB := 9) (by norm_num)
    · rw [hcard, z36OrderNineComplement_card]
    · intro b hb
      exact z36OrderNineComplement_cast4_zero hb
    · exact hAllThree
    · intro b hb b' hb' hne
      exact z36OrderNineComplement_difference_order hb hb' hne
    · norm_num
  · have hAllNine : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 4) = ZMod.cast a' →
        frequencyOrder 36 (a - a') = 9 := by
      intro a ha a' ha' hne hcast
      rcases z36_frequencyOrder_three_or_nine_of_cast4_eq
          a a' hne hcast with horder | horder
      · exact False.elim
          (hthree ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨z36OrderThreeComplement, ?_⟩
    apply tiles_of_cyclic_projection_fiber_opposite_orders
      (N := 36) (m := 4) (rA := 9) (rB := 3) (by norm_num)
    · rw [hcard, z36OrderThreeComplement_card]
    · intro b hb
      exact z36OrderThreeComplement_cast4_zero hb
    · exact hAllNine
    · intro b hb b' hb' hne
      exact z36OrderThreeComplement_difference_order hb hb' hne
    · norm_num

/-- Proposition-valued form consumed by the descent assembly. -/
theorem z36_spectral_card12_implies_tile :
    Z36SpectralCard12ImpliesTile := by
  intro A L hcard hSpec
  exact z36_exists_tiling_of_spectral_card_twelve hSpec hcard

#print axioms z36_exists_tiling_of_spectral_card_twelve
#print axioms z36_spectral_card12_implies_tile

end Fuglede
