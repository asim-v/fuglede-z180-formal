import Fuglede.Z180K18LowOrderInterfaces
import Mathlib.Tactic

/-!
# Kernel-checked order-ten exclusion for the `k = 18`, `m = 2` census

Canonical source: `fuglede_search/z180_k18_closure.py`

* source SHA-256:
  `3b8bb2943e5dfcae8e0439ae606b98d88c42da55b70384a651571274f1ca24b9`
* canonical common-neighbour/color payload SHA-256:
  `6a4f048c907119a93d268134528a185959e668add41d239ddb2b1edb08384292`

Translate an alleged order-ten edge to `{0,d}`.  The remaining sixteen
vertices lie in the common-neighbour graph below.  On that graph the explicit
color `z.val % 11` is proper.  Kernel reduction checks the finite proper-color
statement for all four possible order-ten values of `d`; the abstract proof
then injects sixteen vertices into eleven colors, a contradiction.

The checked proposition is reconstructed from `frequencyOrder` and the
formal envelope literal.  The external payload is therefore reproducibility
metadata, not a trusted premise.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Pointwise common-neighbour predicate.  Keeping it separate avoids making
the finite color checker search through a filtered finset for each lookup. -/
def Z180K18M2HighEdgeCommonNeighbor (d z : ZMod 180) : Prop :=
  z ≠ 0 ∧ z ≠ d ∧
    frequencyOrder 180 z ∈ z180K18M2EnvelopeOrders ∧
    frequencyOrder 180 (z - d) ∈ z180K18M2EnvelopeOrders

instance (d z : ZMod 180) :
    Decidable (Z180K18M2HighEdgeCommonNeighbor d z) := by
  unfold Z180K18M2HighEdgeCommonNeighbor
  infer_instance

/-- Common neighbours of `0` and `d` in the exact `m = 2` envelope graph. -/
def z180K18M2HighEdgeCommonNeighbors (d : ZMod 180) : Finset (ZMod 180) :=
  Finset.univ.filter fun z => Z180K18M2HighEdgeCommonNeighbor d z

/-- Eleven-color certificate used on every order-ten common-neighbour
graph. -/
def z180K18M2HighEdgeColor (z : ZMod 180) : Nat :=
  z.val % 11

/-- The finite kernel certificate that the displayed eleven-coloring is
proper on every relevant common-neighbour graph. -/
theorem z180_k18_m2_highEdgeColor_separates :
    ∀ d : ZMod 180, frequencyOrder 180 d = 10 →
      ∀ z w : ZMod 180,
      Z180K18M2HighEdgeCommonNeighbor d z →
      Z180K18M2HighEdgeCommonNeighbor d w →
      frequencyOrder 180 (z - w) ∈ z180K18M2EnvelopeOrders →
      z ≠ w →
      z180K18M2HighEdgeColor z ≠ z180K18M2HighEdgeColor w := by
  decide

/-- A cardinality-eighteen clique in the `m = 2` envelope cannot contain an
order-ten edge.  This inhabits the exact census interface used by the
terminal branch. -/
theorem z180_k18_m2_noHighEdgeCensus :
    Z180K18M2NoHighEdgeCensusInterface := by
  intro L hcard henv x hx y hy hne horder
  let d : ZMod 180 := x - y
  let K : Finset (ZMod 180) := L.image fun z => z - y
  have hinj : Function.Injective (fun z : ZMod 180 => z - y) :=
    fun _ _ h => sub_left_injective h
  have hcardK : K.card = 18 := by
    change (L.image fun z => z - y).card = 18
    rw [Finset.card_image_of_injective _ hinj, hcard]
  have hzeroK : 0 ∈ K := by
    change 0 ∈ L.image fun z => z - y
    exact Finset.mem_image.mpr ⟨y, hy, sub_self y⟩
  have hdK : d ∈ K := by
    change d ∈ L.image fun z => z - y
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  have henvK : Z180K18DifferenceOrderEnvelope K z180K18M2EnvelopeOrders := by
    intro u hu v hv huv
    obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, hbv⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := by
      intro hab
      apply huv
      rw [← hau, ← hbv, hab]
    have habAllowed := henv a ha b hb hab
    have heq : u - v = a - b := by
      rw [← hau, ← hbv]
      abel
    rw [heq]
    exact habAllowed
  have hcardEraseZero : (K.erase 0).card = 17 := by
    rw [Finset.card_erase_of_mem hzeroK, hcardK]
  have hdEraseZero : d ∈ K.erase 0 :=
    Finset.mem_erase.mpr ⟨hd0, hdK⟩
  let S : Finset (ZMod 180) := (K.erase 0).erase d
  have hcardS : S.card = 16 := by
    change ((K.erase 0).erase d).card = 16
    rw [Finset.card_erase_of_mem hdEraseZero, hcardEraseZero]
  have hSK : S ⊆ K := by
    intro z hz
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  have hsubset : S ⊆ z180K18M2HighEdgeCommonNeighbors d := by
    intro z hz
    have hzd := (Finset.mem_erase.mp hz).1
    have hzEraseZero := (Finset.mem_erase.mp hz).2
    have hz0 := (Finset.mem_erase.mp hzEraseZero).1
    have hzK := hSK hz
    have hzeroAllowed := henvK z hzK 0 hzeroK hz0
    have hdAllowed := henvK z hzK d hdK hzd
    rw [z180K18M2HighEdgeCommonNeighbors, Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    exact ⟨hz0, hzd, by simpa using hzeroAllowed, hdAllowed⟩
  have hdOrder : frequencyOrder 180 d = 10 := by
    simpa [d] using horder
  have hcolorInj :
      Set.InjOn z180K18M2HighEdgeColor (S : Set (ZMod 180)) := by
    intro u hu v hv hcolor
    by_contra huv
    have huvAllowed := henvK u (hSK hu) v (hSK hv) huv
    have huCommon := (Finset.mem_filter.mp (hsubset hu)).2
    have hvCommon := (Finset.mem_filter.mp (hsubset hv)).2
    have hsep := z180_k18_m2_highEdgeColor_separates
      d hdOrder u v huCommon hvCommon huvAllowed huv
    exact hsep hcolor
  have hcardColors :
      (S.image z180K18M2HighEdgeColor).card = 16 := by
    rw [Finset.card_image_iff.mpr hcolorInj, hcardS]
  have hcolors : S.image z180K18M2HighEdgeColor ⊆ Finset.range 11 := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  have hle := Finset.card_le_card hcolors
  rw [hcardColors, Finset.card_range] at hle
  omega

#print axioms z180_k18_m2_highEdgeColor_separates
#print axioms z180_k18_m2_noHighEdgeCensus

end Fuglede
