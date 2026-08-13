import Fuglede.Z180K18M6GraphLargeCounting

/-!
# Anchoring a large fifth-coordinate fibre

A fibre with at least three vertices contains a triangle.  The local CRT
kernels make the whole main fibre vertical and force every outside vertex to
have the opposite modulo-four parity.
-/

namespace Fuglede

theorem z180_k18_m6_same_of_pairwise_allowed
    {L : Finset (ZMod 180)} (hpair : Z180K18M6PairwiseAllowed L)
    {x y : ZMod 180} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x = z180K18M6Fifth y) :
    Z180K18M6SameLevelCompatible
      (z180K18M6BaseCoord x) (z180K18M6BaseCoord y) := by
  have hrel := (z180_k18_m6_allowed_iff_crt_relation x y).mp
    (hpair x hx y hy hxy)
  simpa [hfifth] using hrel

theorem z180_k18_m6_cross_of_pairwise_allowed
    {L : Finset (ZMod 180)} (hpair : Z180K18M6PairwiseAllowed L)
    {x y : ZMod 180} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x ≠ z180K18M6Fifth y) :
    Z180K18M6CrossLevelCompatible
      (z180K18M6BaseCoord x) (z180K18M6BaseCoord y) := by
  have hrel := (z180_k18_m6_allowed_iff_crt_relation x y).mp
    (hpair x hx y hy hxy)
  simpa [hfifth] using hrel

theorem z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth
    {x y : ZMod 180} (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x = z180K18M6Fifth y) :
    z180K18M6BaseCoord x ≠ z180K18M6BaseCoord y := by
  intro hbase
  apply hxy
  apply z180_k18_m6_crt_coordinates_injective
  exact Prod.ext hbase hfifth

theorem z180_k18_m6_large_fibre_anchor
    (L : Finset (ZMod 180)) (hpair : Z180K18M6PairwiseAllowed L)
    (c : ZMod 5) (hc : 3 ≤ (z180K18M6Fibre L c).card) :
    ∃ x ∈ z180K18M6Fibre L c,
      ∃ p ∈ z180K18M6Fibre L c,
      ∃ q ∈ z180K18M6Fibre L c,
        x ≠ p ∧ x ≠ q ∧ p ≠ q ∧
        (∀ z ∈ z180K18M6Fibre L c,
          (z180K18M6BaseCoord z).1 = (z180K18M6BaseCoord x).1) ∧
        (∀ z ∈ z180K18M6OutsideFibre L c,
          z180K18M6Parity (z180K18M6BaseCoord x) ≠
            z180K18M6Parity (z180K18M6BaseCoord z)) := by
  classical
  have hthree : 2 < (z180K18M6Fibre L c).card := by omega
  obtain ⟨x, p, q, hx, hp, hq, hxp, hxq, hpq⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have hx' := Finset.mem_filter.mp hx
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hsxp := z180_k18_m6_same_of_pairwise_allowed hpair
    hx'.1 hp'.1 hxp (hx'.2.trans hp'.2.symm)
  have hsxq := z180_k18_m6_same_of_pairwise_allowed hpair
    hx'.1 hq'.1 hxq (hx'.2.trans hq'.2.symm)
  have hspq := z180_k18_m6_same_of_pairwise_allowed hpair
    hp'.1 hq'.1 hpq (hp'.2.trans hq'.2.symm)
  have hbpu := z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth hxp
    (hx'.2.trans hp'.2.symm)
  have hbqu := z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth hxq
    (hx'.2.trans hq'.2.symm)
  have hbpq := z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth hpq
    (hp'.2.trans hq'.2.symm)
  have hvertical := z180_k18_m6_same_level_triangle_vertical_general
    _ _ _ hbpu hbqu hbpq hsxp hsxq hspq
  refine ⟨x, hx, p, hp, q, hq, hxp, hxq, hpq, ?_, ?_⟩
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzp : z = p
    · simpa [hzp] using hvertical.1.symm
    have hbxz := z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth hzx
      (hz'.2.trans hx'.2.symm)
    have hbpz := z180_k18_m6_baseCoord_ne_of_ne_of_same_fifth hzp
      (hz'.2.trans hp'.2.symm)
    have hsxz := z180_k18_m6_same_of_pairwise_allowed hpair
      hz'.1 hx'.1 hzx (hz'.2.trans hx'.2.symm)
    have hspz := z180_k18_m6_same_of_pairwise_allowed hpair
      hz'.1 hp'.1 hzp (hz'.2.trans hp'.2.symm)
    have hv := z180_k18_m6_same_level_triangle_vertical_general
      (z180K18M6BaseCoord z) (z180K18M6BaseCoord x)
      (z180K18M6BaseCoord p) hbxz hbpz hbpu
      hsxz hspz hsxp
    exact hv.1
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzx5 : z180K18M6Fifth x ≠ z180K18M6Fifth z := by
      simpa [hx'.2] using (Ne.symm hz'.2)
    have hzp5 : z180K18M6Fifth p ≠ z180K18M6Fifth z := by
      simpa [hp'.2] using (Ne.symm hz'.2)
    have hzq5 : z180K18M6Fifth q ≠ z180K18M6Fifth z := by
      simpa [hq'.2] using (Ne.symm hz'.2)
    have hzx : x ≠ z := fun h => hzx5 (congrArg z180K18M6Fifth h)
    have hzp : p ≠ z := fun h => hzp5 (congrArg z180K18M6Fifth h)
    have hzq : q ≠ z := fun h => hzq5 (congrArg z180K18M6Fifth h)
    have hcxz := z180_k18_m6_cross_of_pairwise_allowed hpair
      hx'.1 hz'.1 hzx hzx5
    have hcpz := z180_k18_m6_cross_of_pairwise_allowed hpair
      hp'.1 hz'.1 hzp hzp5
    have hcqz := z180_k18_m6_cross_of_pairwise_allowed hpair
      hq'.1 hz'.1 hzq hzq5
    exact z180_k18_m6_triangle_forces_cross_parity_general
      _ _ _ _ hbpu hbqu hbpq hsxp hsxq hspq hcxz hcpz hcqz

#print axioms z180_k18_m6_large_fibre_anchor

end Fuglede
