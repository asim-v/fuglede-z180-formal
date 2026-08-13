import Fuglede.Z180K18M6GraphCounting

/-!
# The all-small-fibres geometry in the K18 `m = 6` graph

Three fifth-coordinate fibres cannot each contain a compatible pair.  The
proof selects one pair from each fibre and applies the translated local
double-fibre kernel three times.
-/

namespace Fuglede

private theorem same_of_pairwise_allowed
    {L : Finset (ZMod 180)} (hpair : Z180K18M6PairwiseAllowed L)
    {x y : ZMod 180} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x = z180K18M6Fifth y) :
    Z180K18M6SameLevelCompatible
      (z180K18M6BaseCoord x) (z180K18M6BaseCoord y) := by
  have hallowed := hpair x hx y hy hxy
  have hrel := (z180_k18_m6_allowed_iff_crt_relation x y).mp hallowed
  simpa [hfifth] using hrel

private theorem cross_of_pairwise_allowed
    {L : Finset (ZMod 180)} (hpair : Z180K18M6PairwiseAllowed L)
    {x y : ZMod 180} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x ≠ z180K18M6Fifth y) :
    Z180K18M6CrossLevelCompatible
      (z180K18M6BaseCoord x) (z180K18M6BaseCoord y) := by
  have hallowed := hpair x hx y hy hxy
  have hrel := (z180_k18_m6_allowed_iff_crt_relation x y).mp hallowed
  simpa [hfifth] using hrel

private theorem baseCoord_ne_of_ne_of_same_fifth
    {x y : ZMod 180} (hxy : x ≠ y)
    (hfifth : z180K18M6Fifth x = z180K18M6Fifth y) :
    z180K18M6BaseCoord x ≠ z180K18M6BaseCoord y := by
  intro hbase
  apply hxy
  apply z180_k18_m6_crt_coordinates_injective
  exact Prod.ext hbase hfifth

private theorem zmod2_eq_of_both_ne :
    ∀ a b c : ZMod 2, a ≠ b → a ≠ c → b = c := by
  decide

theorem z180_k18_m6_double_fibre_card_le_two_of_pairwise_allowed
    (L : Finset (ZMod 180)) (hpair : Z180K18M6PairwiseAllowed L) :
    Z180K18M6DoubleFibreBound L := by
  classical
  let D := z180K18M6DoubleFibres L
  change D.card ≤ 2
  by_contra hD
  have hthree : 2 < D.card := by omega
  obtain ⟨c0, c1, c2, hc0D, hc1D, hc2D, hc01, hc02, hc12⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have hc0 : 1 < (z180K18M6Fibre L c0).card := by
    have := (Finset.mem_filter.mp hc0D).2
    omega
  have hc1 : 1 < (z180K18M6Fibre L c1).card := by
    have := (Finset.mem_filter.mp hc1D).2
    omega
  have hc2 : 1 < (z180K18M6Fibre L c2).card := by
    have := (Finset.mem_filter.mp hc2D).2
    omega
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := Finset.one_lt_card.mp hc0
  obtain ⟨x1, hx1, y1, hy1, hxy1⟩ := Finset.one_lt_card.mp hc1
  obtain ⟨x2, hx2, y2, hy2, hxy2⟩ := Finset.one_lt_card.mp hc2
  have hx0' := Finset.mem_filter.mp hx0
  have hy0' := Finset.mem_filter.mp hy0
  have hx1' := Finset.mem_filter.mp hx1
  have hy1' := Finset.mem_filter.mp hy1
  have hx2' := Finset.mem_filter.mp hx2
  have hy2' := Finset.mem_filter.mp hy2
  have hs0 := same_of_pairwise_allowed hpair hx0'.1 hy0'.1 hxy0
    (hx0'.2.trans hy0'.2.symm)
  have hs1 := same_of_pairwise_allowed hpair hx1'.1 hy1'.1 hxy1
    (hx1'.2.trans hy1'.2.symm)
  have hs2 := same_of_pairwise_allowed hpair hx2'.1 hy2'.1 hxy2
    (hx2'.2.trans hy2'.2.symm)
  have hcross {u v : ZMod 180}
      (hu : u ∈ L) (hv : v ∈ L)
      {cu cv : ZMod 5} (huc : z180K18M6Fifth u = cu)
      (hvc : z180K18M6Fifth v = cv) (hcv : cu ≠ cv) :
      Z180K18M6CrossLevelCompatible
        (z180K18M6BaseCoord u) (z180K18M6BaseCoord v) := by
    have huv5 : z180K18M6Fifth u ≠ z180K18M6Fifth v := by
      intro h
      exact hcv (huc.symm.trans (h.trans hvc))
    have huv : u ≠ v := by
      intro h
      subst v
      exact huv5 rfl
    exact cross_of_pairwise_allowed hpair hu hv huv huv5
  have h01a := hcross hx0'.1 hx1'.1 hx0'.2 hx1'.2 hc01
  have h01b := hcross hx0'.1 hy1'.1 hx0'.2 hy1'.2 hc01
  have h01c := hcross hy0'.1 hx1'.1 hy0'.2 hx1'.2 hc01
  have h01d := hcross hy0'.1 hy1'.1 hy0'.2 hy1'.2 hc01
  have h02a := hcross hx0'.1 hx2'.1 hx0'.2 hx2'.2 hc02
  have h02b := hcross hx0'.1 hy2'.1 hx0'.2 hy2'.2 hc02
  have h02c := hcross hy0'.1 hx2'.1 hy0'.2 hx2'.2 hc02
  have h02d := hcross hy0'.1 hy2'.1 hy0'.2 hy2'.2 hc02
  have h12a := hcross hx1'.1 hx2'.1 hx1'.2 hx2'.2 hc12
  have h12b := hcross hx1'.1 hy2'.1 hx1'.2 hy2'.2 hc12
  have h12c := hcross hy1'.1 hx2'.1 hy1'.2 hx2'.2 hc12
  have h12d := hcross hy1'.1 hy2'.1 hy1'.2 hy2'.2 hc12
  have hb0 := baseCoord_ne_of_ne_of_same_fifth hxy0
    (hx0'.2.trans hy0'.2.symm)
  have hb1 := baseCoord_ne_of_ne_of_same_fifth hxy1
    (hx1'.2.trans hy1'.2.symm)
  have hb2 := baseCoord_ne_of_ne_of_same_fifth hxy2
    (hx2'.2.trans hy2'.2.symm)
  have hp01 := z180_k18_m6_compatible_double_fibres_general
    _ _ _ _ hb0 hb1 hs0 hs1 h01a h01b h01c h01d
  have hp02 := z180_k18_m6_compatible_double_fibres_general
    _ _ _ _ hb0 hb2 hs0 hs2 h02a h02b h02c h02d
  have hp12 := z180_k18_m6_compatible_double_fibres_general
    _ _ _ _ hb1 hb2 hs1 hs2 h12a h12b h12c h12d
  have heq := zmod2_eq_of_both_ne
    (z180K18M6Parity (z180K18M6BaseCoord x0))
    (z180K18M6Parity (z180K18M6BaseCoord x1))
    (z180K18M6Parity (z180K18M6BaseCoord x2)) hp01.2.2 hp02.2.2
  exact hp12.2.2 heq

#print axioms z180_k18_m6_double_fibre_card_le_two_of_pairwise_allowed

end Fuglede
