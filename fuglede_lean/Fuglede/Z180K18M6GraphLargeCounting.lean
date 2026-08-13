import Fuglede.Z180K18M6GraphSmallGeometry

/-!
# Counting assembly for a large fifth-coordinate fibre

The remaining geometry has two possible outputs.  In the two-level regime,
each modulo-three column contains at most three vertices in total.  In the
multi-level regime, the main fibre has at most six vertices and its outside
has at most three.  Either output gives the global bound nine by generic
fibre counting.
-/

namespace Fuglede

open scoped BigOperators

def z180K18M6OutsideFibre
    (L : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 180) :=
  L.filter fun x => z180K18M6Fifth x ≠ c

def z180K18M6ThirdFibre
    (S : Finset (ZMod 180)) (r : ZMod 3) : Finset (ZMod 180) :=
  S.filter fun x => z180K18M6Third (z180K18M6BaseCoord x) = r

theorem z180_k18_m6_sum_third_fibre_cards (S : Finset (ZMod 180)) :
    (∑ r : ZMod 3, (z180K18M6ThirdFibre S r).card) = S.card := by
  classical
  simpa [z180K18M6ThirdFibre] using
    (Finset.sum_card_fiberwise_eq_card_filter S
      (Finset.univ : Finset (ZMod 3))
      (fun x : ZMod 180 => z180K18M6Third (z180K18M6BaseCoord x)))

theorem z180_k18_m6_main_add_outside_card
    (L : Finset (ZMod 180)) (c : ZMod 5) :
    (z180K18M6Fibre L c).card + (z180K18M6OutsideFibre L c).card = L.card := by
  classical
  simpa [z180K18M6Fibre, z180K18M6OutsideFibre] using
    (Finset.card_filter_add_card_filter_not (s := L)
      (fun x => z180K18M6Fifth x = c))

/-- The exact geometric output still required for one large fibre. -/
def Z180K18M6LargeFibreProfileAt
    (L : Finset (ZMod 180)) (c : ZMod 5) : Prop :=
  (∀ r : ZMod 3,
      (z180K18M6ThirdFibre (z180K18M6Fibre L c) r).card +
        (z180K18M6ThirdFibre (z180K18M6OutsideFibre L c) r).card ≤ 3) ∨
    ((z180K18M6Fibre L c).card ≤ 6 ∧
      (z180K18M6OutsideFibre L c).card ≤ 3)

/-- Honest remaining large-fibre geometric certificate. -/
def Z180K18M6LargeFibreProfileCertificate : Prop :=
  ∀ L : Finset (ZMod 180),
    Z180K18M6PairwiseAllowed L →
    ∀ c : ZMod 5, 3 ≤ (z180K18M6Fibre L c).card →
      Z180K18M6LargeFibreProfileAt L c

theorem z180_k18_m6_card_le_nine_of_large_fibre_profile
    (L : Finset (ZMod 180)) (c : ZMod 5)
    (hprofile : Z180K18M6LargeFibreProfileAt L c) :
    L.card ≤ 9 := by
  rcases hprofile with hcolumns | hsixthree
  · have hle :
        (∑ r : ZMod 3,
          ((z180K18M6ThirdFibre (z180K18M6Fibre L c) r).card +
           (z180K18M6ThirdFibre (z180K18M6OutsideFibre L c) r).card)) ≤
          ∑ _r : ZMod 3, 3 := by
      exact Finset.sum_le_sum fun r _ => hcolumns r
    rw [Finset.sum_add_distrib,
      z180_k18_m6_sum_third_fibre_cards,
      z180_k18_m6_sum_third_fibre_cards] at hle
    have hsplit := z180_k18_m6_main_add_outside_card L c
    norm_num at hle ⊢
    omega
  · have hsplit := z180_k18_m6_main_add_outside_card L c
    omega

#print axioms z180_k18_m6_sum_third_fibre_cards
#print axioms z180_k18_m6_main_add_outside_card
#print axioms z180_k18_m6_card_le_nine_of_large_fibre_profile

end Fuglede
