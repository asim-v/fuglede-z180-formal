import Fuglede.Z180K18M6GraphLargeGeometryPrelude

/-!
# Closing the large-fibre profile

Once a large fibre is anchored, reduction modulo nine is injective both on
the main fibre and on its outside.  In each modulo-three column, either one
side is empty (giving the ambient bound three) or cross compatibility forces
both sides to be singletons.  Thus every combined column has size at most
three.
-/

namespace Fuglede

theorem z180_k18_m6_card_z9_third_fibre :
    ∀ r : ZMod 3,
      ((Finset.univ : Finset (ZMod 9)).filter fun b =>
        (ZMod.cast b : ZMod 3) = r).card = 3 := by
  decide

private theorem card_le_three_of_ninth_inj_same_third
    (S : Finset (ZMod 180)) (r : ZMod 3)
    (hinj : ∀ x ∈ S, ∀ y ∈ S,
      (z180K18M6BaseCoord x).2 = (z180K18M6BaseCoord y).2 → x = y)
    (hthird : ∀ x ∈ S, z180K18M6Third (z180K18M6BaseCoord x) = r) :
    S.card ≤ 3 := by
  classical
  let image9 := S.image fun x => (z180K18M6BaseCoord x).2
  have hinjOn : Set.InjOn (fun x : ZMod 180 => (z180K18M6BaseCoord x).2) S := by
    intro x hx y hy hxy
    exact hinj x hx y hy hxy
  have hcard : image9.card = S.card := by
    exact Finset.card_image_iff.mpr hinjOn
  have hsubset : image9 ⊆
      (Finset.univ : Finset (ZMod 9)).filter fun b =>
        (ZMod.cast b : ZMod 3) = r := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthird x hx⟩
  have hle := Finset.card_le_card hsubset
  rw [z180_k18_m6_card_z9_third_fibre r] at hle
  omega

private theorem zmod2_eq_of_both_ne
    (a b c : ZMod 2) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

theorem z180_k18_m6_large_fibre_profile_of_pairwise_allowed
    (L : Finset (ZMod 180)) (hpair : Z180K18M6PairwiseAllowed L)
    (c : ZMod 5) (hc : 3 ≤ (z180K18M6Fibre L c).card) :
    Z180K18M6LargeFibreProfileAt L c := by
  classical
  obtain ⟨anchor, hanchor, p, hp, q, hq, hanchorP, hanchorQ, hpq,
    hmainFourth, houtParity⟩ :=
    z180_k18_m6_large_fibre_anchor L hpair c hc
  have hanchor' := Finset.mem_filter.mp hanchor
  have hninthMain : ∀ u ∈ z180K18M6Fibre L c,
      ∀ v ∈ z180K18M6Fibre L c,
      (z180K18M6BaseCoord u).2 = (z180K18M6BaseCoord v).2 → u = v := by
    intro u hu v hv huv9
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    apply z180_k18_m6_crt_coordinates_injective
    apply Prod.ext
    · apply Prod.ext
      · exact (hmainFourth u hu).trans (hmainFourth v hv).symm
      · exact huv9
    · exact hu'.2.trans hv'.2.symm
  have hninthOutside : ∀ u ∈ z180K18M6OutsideFibre L c,
      ∀ v ∈ z180K18M6OutsideFibre L c,
      (z180K18M6BaseCoord u).2 = (z180K18M6BaseCoord v).2 → u = v := by
    intro u hu v hv huv9
    by_contra huv
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    have hpar : z180K18M6Parity (z180K18M6BaseCoord u) =
        z180K18M6Parity (z180K18M6BaseCoord v) :=
      zmod2_eq_of_both_ne
        (z180K18M6Parity (z180K18M6BaseCoord anchor)) _ _
        (houtParity u hu) (houtParity v hv)
    by_cases huv5 : z180K18M6Fifth u = z180K18M6Fifth v
    · have hs := z180_k18_m6_same_of_pairwise_allowed hpair
        hu'.1 hv'.1 huv huv5
      rcases hs with hvertical | hhorizontal
      · exact hvertical.2 huv9
      · exact hhorizontal.2 hpar
    · have hx := z180_k18_m6_cross_of_pairwise_allowed hpair
        hu'.1 hv'.1 huv huv5
      rcases hx with hsame | hopp
      · exact hsame.2.2 huv9
      · exact hopp.1 hpar
  left
  intro r
  let M := z180K18M6ThirdFibre (z180K18M6Fibre L c) r
  let O := z180K18M6ThirdFibre (z180K18M6OutsideFibre L c) r
  have hMthree : M.card ≤ 3 := by
    apply card_le_three_of_ninth_inj_same_third M r
    · intro u hu v hv huv9
      exact hninthMain u (Finset.mem_filter.mp hu).1
        v (Finset.mem_filter.mp hv).1 huv9
    · intro u hu
      exact (Finset.mem_filter.mp hu).2
  have hOthree : O.card ≤ 3 := by
    apply card_le_three_of_ninth_inj_same_third O r
    · intro u hu v hv huv9
      exact hninthOutside u (Finset.mem_filter.mp hu).1
        v (Finset.mem_filter.mp hv).1 huv9
    · intro u hu
      exact (Finset.mem_filter.mp hu).2
  by_cases hM : M = ∅
  · simp [M, O, hM]
    exact hOthree
  by_cases hO : O = ∅
  · simp [M, O, hO]
    exact hMthree
  have hMne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM
  have hOne : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr hO
  obtain ⟨u, huM⟩ := hMne
  obtain ⟨v, hvO⟩ := hOne
  have huM' := Finset.mem_filter.mp huM
  have hvO' := Finset.mem_filter.mp hvO
  have hu' := Finset.mem_filter.mp huM'.1
  have hv' := Finset.mem_filter.mp hvO'.1
  have huv5 : z180K18M6Fifth u ≠ z180K18M6Fifth v := by
    simpa [hu'.2] using (Ne.symm hv'.2)
  have huv : u ≠ v := fun h => huv5 (congrArg z180K18M6Fifth h)
  have hcrossUV := z180_k18_m6_cross_of_pairwise_allowed hpair
    hu'.1 hv'.1 huv huv5
  have hparUV : z180K18M6Parity (z180K18M6BaseCoord u) ≠
      z180K18M6Parity (z180K18M6BaseCoord v) := by
    rw [show z180K18M6Parity (z180K18M6BaseCoord u) =
      z180K18M6Parity (z180K18M6BaseCoord anchor) by
        simp [z180K18M6Parity, hmainFourth u huM'.1]]
    exact houtParity v hvO'.1
  have huv9 := z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
    hcrossUV hparUV (huM'.2.trans hvO'.2.symm)
  have hMone : M.card ≤ 1 := Finset.card_le_one_iff.mpr (by
    intro a b ha hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply hninthMain a ha'.1 b hb'.1
    have haL := Finset.mem_filter.mp ha'.1
    have hbL := Finset.mem_filter.mp hb'.1
    have hav5 : z180K18M6Fifth a ≠ z180K18M6Fifth v := by
      simpa [haL.2] using (Ne.symm hv'.2)
    have hbv5 : z180K18M6Fifth b ≠ z180K18M6Fifth v := by
      simpa [hbL.2] using (Ne.symm hv'.2)
    have hav : a ≠ v := fun h => hav5 (congrArg z180K18M6Fifth h)
    have hbv : b ≠ v := fun h => hbv5 (congrArg z180K18M6Fifth h)
    have hca := z180_k18_m6_cross_of_pairwise_allowed hpair
      haL.1 hv'.1 hav hav5
    have hcb := z180_k18_m6_cross_of_pairwise_allowed hpair
      hbL.1 hv'.1 hbv hbv5
    have hpa : z180K18M6Parity (z180K18M6BaseCoord a) ≠
        z180K18M6Parity (z180K18M6BaseCoord v) := by
      rw [show z180K18M6Parity (z180K18M6BaseCoord a) =
        z180K18M6Parity (z180K18M6BaseCoord anchor) by
          simp [z180K18M6Parity, hmainFourth a ha'.1]]
      exact houtParity v hvO'.1
    have hpb : z180K18M6Parity (z180K18M6BaseCoord b) ≠
        z180K18M6Parity (z180K18M6BaseCoord v) := by
      rw [show z180K18M6Parity (z180K18M6BaseCoord b) =
        z180K18M6Parity (z180K18M6BaseCoord anchor) by
          simp [z180K18M6Parity, hmainFourth b hb'.1]]
      exact houtParity v hvO'.1
    have ha9 := z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
      hca hpa (ha'.2.trans hvO'.2.symm)
    have hb9 := z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
      hcb hpb (hb'.2.trans hvO'.2.symm)
    exact ha9.trans hb9.symm)
  have hOone : O.card ≤ 1 := Finset.card_le_one_iff.mpr (by
    intro a b ha hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply hninthOutside a ha'.1 b hb'.1
    have haL := Finset.mem_filter.mp ha'.1
    have hbL := Finset.mem_filter.mp hb'.1
    have hua5 : z180K18M6Fifth u ≠ z180K18M6Fifth a := by
      simpa [hu'.2] using (Ne.symm (Finset.mem_filter.mp ha'.1).2)
    have hub5 : z180K18M6Fifth u ≠ z180K18M6Fifth b := by
      simpa [hu'.2] using (Ne.symm (Finset.mem_filter.mp hb'.1).2)
    have hua : u ≠ a := fun h => hua5 (congrArg z180K18M6Fifth h)
    have hub : u ≠ b := fun h => hub5 (congrArg z180K18M6Fifth h)
    have hca := z180_k18_m6_cross_of_pairwise_allowed hpair
      hu'.1 haL.1 hua hua5
    have hcb := z180_k18_m6_cross_of_pairwise_allowed hpair
      hu'.1 hbL.1 hub hub5
    have hpa : z180K18M6Parity (z180K18M6BaseCoord u) ≠
        z180K18M6Parity (z180K18M6BaseCoord a) := by
      rw [show z180K18M6Parity (z180K18M6BaseCoord u) =
        z180K18M6Parity (z180K18M6BaseCoord anchor) by
          simp [z180K18M6Parity, hmainFourth u huM'.1]]
      exact houtParity a ha'.1
    have hpb : z180K18M6Parity (z180K18M6BaseCoord u) ≠
        z180K18M6Parity (z180K18M6BaseCoord b) := by
      rw [show z180K18M6Parity (z180K18M6BaseCoord u) =
        z180K18M6Parity (z180K18M6BaseCoord anchor) by
          simp [z180K18M6Parity, hmainFourth u huM'.1]]
      exact houtParity b hb'.1
    have ha9 := z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
      hca hpa (huM'.2.trans ha'.2.symm)
    have hb9 := z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
      hcb hpb (huM'.2.trans hb'.2.symm)
    exact ha9.symm.trans hb9)
  change M.card + O.card ≤ 3
  omega

theorem z180_k18_m6_large_fibre_profile_certificate :
    Z180K18M6LargeFibreProfileCertificate := by
  intro L hpair c hc
  exact z180_k18_m6_large_fibre_profile_of_pairwise_allowed L hpair c hc

#print axioms z180_k18_m6_large_fibre_profile_of_pairwise_allowed
#print axioms z180_k18_m6_large_fibre_profile_certificate

end Fuglede
