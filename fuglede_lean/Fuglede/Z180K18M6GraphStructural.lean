import Fuglede.Z180K18M6GraphLargeGeometry

/-!
# Structural assembly for the cardinality-eighteen `m = 6` graph

This module assembles the two fibre regimes into clique number at most nine.
It does not claim that the spectral hypotheses imply the seven-order zero
envelope, and it does not assert the terminal tiling branch.
-/

namespace Fuglede

theorem z180_k18_m6_card_le_nine_of_fibre_bounds
    (L : Finset (ZMod 180))
    (hlarge : Z180K18M6LargeFibreBound L)
    (hsmall : Z180K18M6SmallFibresBound L) :
    L.card ≤ 9 := by
  by_cases h : ∀ c : ZMod 5, (z180K18M6Fibre L c).card ≤ 2
  · exact (hsmall h).trans (by norm_num)
  · push_neg at h
    obtain ⟨c, hc⟩ := h
    apply hlarge c
    omega

theorem z180_k18_m6_card_le_nine_of_pairwise_allowed
    (L : Finset (ZMod 180))
    (hpair : Z180K18M6PairwiseAllowed L) :
    L.card ≤ 9 := by
  have hlarge : Z180K18M6LargeFibreBound L := by
    intro c hc
    exact z180_k18_m6_card_le_nine_of_large_fibre_profile L c
      (z180_k18_m6_large_fibre_profile_of_pairwise_allowed L hpair c hc)
  have hdouble :=
    z180_k18_m6_double_fibre_card_le_two_of_pairwise_allowed L hpair
  have hsmall : Z180K18M6SmallFibresBound L := by
    intro hall
    exact z180_k18_m6_small_fibres_card_le_seven L hall hdouble
  exact z180_k18_m6_card_le_nine_of_fibre_bounds L hlarge hsmall

#print axioms z180_k18_m6_card_le_nine_of_fibre_bounds
#print axioms z180_k18_m6_card_le_nine_of_pairwise_allowed

end Fuglede
