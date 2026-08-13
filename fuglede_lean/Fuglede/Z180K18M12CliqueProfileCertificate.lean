import Fuglede.Z180K18M12UnwantedColorShard0
import Fuglede.Z180K18M12UnwantedColorShard1
import Fuglede.Z180K18M12UnwantedColorShard2
import Fuglede.Z180K18M12MissingOrderColorShard0
import Fuglede.Z180K18M12MissingOrderColorShard1
import Fuglede.Z180K18M12MissingOrderColorShard2
import Fuglede.Z180K18M12MissingOrderColorShard3
import Fuglede.Z180K18M12MissingOrderColorShard4
import Fuglede.Z180K18LowOrderInterfaces
import Mathlib.Tactic

/-!
# Sharded kernel certificate for the `k = 18`, `m = 12` clique profile

The eight expensive finite checks are fixed-index leaves.  This aggregator
uses `fin_cases` to recover the two public proper-color theorems and contains
all remaining abstract glue:

* three unwanted-edge colorings give profile containment;
* five missing-order colorings give realization of every profile order;
* together they inhabit `Z180K18M12CliqueCensusInterface`.

Canonical source SHA-256:
`3b8bb2943e5dfcae8e0439ae606b98d88c42da55b70384a651571274f1ca24b9`

Canonical four-clique payload SHA-256:
`c191c2de1ee5eb6ecc5754c61045329a3caeb85f21f3a136de5fee6d8195ea4d`

Canonical coloring payload SHA-256:
`4f81b50bda56102c633827455b0608e24c855b6c559982971f8e30146b13f46c`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Dispatch the three fixed-index unwanted-edge shards. -/
theorem z180_k18_m12_unwantedColor_separates :
    ∀ i : Fin 3, ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder i →
      ∀ z w : ZMod 180,
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor i d z ≠
          z180K18M12UnwantedColor i d w := by
  intro i
  fin_cases i
  · exact z180_k18_m12_unwantedColor_separates_shard_0
  · exact z180_k18_m12_unwantedColor_separates_shard_1
  · exact z180_k18_m12_unwantedColor_separates_shard_2

/-- Dispatch the five fixed-index missing-order shards. -/
theorem z180_k18_m12_missingOrderColor_separates :
    ∀ i : Fin 5, ∀ z w : ZMod 180,
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder i →
      z ≠ w →
      z180K18M12MissingOrderColor i z ≠
        z180K18M12MissingOrderColor i w := by
  intro i
  fin_cases i
  · exact z180_k18_m12_missingOrderColor_separates_shard_0
  · exact z180_k18_m12_missingOrderColor_separates_shard_1
  · exact z180_k18_m12_missingOrderColor_separates_shard_2
  · exact z180_k18_m12_missingOrderColor_separates_shard_3
  · exact z180_k18_m12_missingOrderColor_separates_shard_4

private theorem z180_k18_differenceEnvelope_translate
    {L : Finset (ZMod 180)} {orders : Finset Nat}
    (henv : Z180K18DifferenceOrderEnvelope L orders)
    (y : ZMod 180) :
    Z180K18DifferenceOrderEnvelope (L.image fun z => z - y) orders := by
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

/-- A size-eighteen envelope clique contains no edge carrying the selected
unwanted order. -/
private theorem z180_k18_m12_no_unwanted_edge
    (i : Fin 3) {L : Finset (ZMod 180)}
    (hcard : L.card = 18)
    (henv : Z180K18M12DifferenceEnvelope L) :
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 180 (x - y) ≠ z180K18M12UnwantedOrder i := by
  intro x hx y hy hne horder
  let d : ZMod 180 := x - y
  let K : Finset (ZMod 180) := L.image fun z => z - y
  have hinj : Function.Injective (fun z : ZMod 180 => z - y) :=
    fun u v h => sub_left_injective h
  have hcardK : K.card = 18 := by
    dsimp only [K]
    rw [Finset.card_image_of_injective _ hinj, hcard]
  have hzeroK : 0 ∈ K := by
    dsimp only [K]
    exact Finset.mem_image.mpr ⟨y, hy, sub_self y⟩
  have hdK : d ∈ K := by
    dsimp only [K]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  have henvK :
      Z180K18DifferenceOrderEnvelope K z180K18M12EnvelopeOrders :=
    z180_k18_differenceEnvelope_translate henv y
  have hcardEraseZero : (K.erase 0).card = 17 := by
    rw [Finset.card_erase_of_mem hzeroK, hcardK]
  have hdEraseZero : d ∈ K.erase 0 :=
    Finset.mem_erase.mpr ⟨hd0, hdK⟩
  let S : Finset (ZMod 180) := (K.erase 0).erase d
  have hcardS : S.card = 16 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem hdEraseZero, hcardEraseZero]
  have hSK : S ⊆ K := by
    intro z hz
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  have hcommon : ∀ z ∈ S, Z180K18M12UnwantedCommonNeighbor d z := by
    intro z hz
    have hzd := (Finset.mem_erase.mp hz).1
    have hzEraseZero := (Finset.mem_erase.mp hz).2
    have hz0 := (Finset.mem_erase.mp hzEraseZero).1
    have hzK := hSK hz
    have hzeroAllowed := henvK z hzK 0 hzeroK hz0
    have hdAllowed := henvK z hzK d hdK hzd
    exact ⟨hz0, hzd, by simpa using hzeroAllowed, hdAllowed⟩
  have hdOrder : frequencyOrder 180 d = z180K18M12UnwantedOrder i := by
    simpa [d] using horder
  have hcolorInj :
      Set.InjOn (z180K18M12UnwantedColor i d) (S : Set (ZMod 180)) := by
    intro u hu v hv hcolor
    by_contra huv
    have huvAllowed := henvK u (hSK hu) v (hSK hv) huv
    have hsep := z180_k18_m12_unwantedColor_separates
      i d hdOrder u v (hcommon u hu) (hcommon v hv) huvAllowed huv
    exact hsep hcolor
  have hcardColors :
      (S.image (z180K18M12UnwantedColor i d)).card = 16 := by
    rw [Finset.card_image_iff.mpr hcolorInj, hcardS]
  have hcolors : S.image (z180K18M12UnwantedColor i d) ⊆
      Finset.range (z180K18M12UnwantedColorBound i) := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (z180_k18_m12_unwantedColor_lt i d z)
  have hle := Finset.card_le_card hcolors
  have hbound := z180_k18_m12_unwantedColorBound_lt_sixteen i
  rw [hcardColors, Finset.card_range] at hle
  omega

/-- Every nonzero difference of a size-eighteen envelope clique lies in the
five-order target profile. -/
theorem z180_k18_m12_profile_containment
    {L : Finset (ZMod 180)}
    (hcard : L.card = 18)
    (henv : Z180K18M12DifferenceEnvelope L) :
    ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 180 (x - y) ∈ z180K18M12ProfileOrders := by
  intro x hx y hy hne
  have hallowed := henv x hx y hy hne
  have hno2 : frequencyOrder 180 (x - y) ≠ 2 := by
    simpa [z180K18M12UnwantedOrder] using
      z180_k18_m12_no_unwanted_edge (0 : Fin 3) hcard henv x hx y hy hne
  have hno15 : frequencyOrder 180 (x - y) ≠ 15 := by
    simpa [z180K18M12UnwantedOrder] using
      z180_k18_m12_no_unwanted_edge (1 : Fin 3) hcard henv x hx y hy hne
  have hno60 : frequencyOrder 180 (x - y) ≠ 60 := by
    simpa [z180K18M12UnwantedOrder] using
      z180_k18_m12_no_unwanted_edge (2 : Fin 3) hcard henv x hx y hy hne
  simpa [z180K18M12EnvelopeOrders, z180K18M12ProfileOrders,
    hno2, hno15, hno60] using hallowed

/-- If all differences lie in the target profile, the selected required
order must actually occur. -/
private theorem z180_k18_m12_required_order_realized
    (i : Fin 5) {L : Finset (ZMod 180)}
    (hcard : L.card = 18)
    (hcontained :
      ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
        frequencyOrder 180 (x - y) ∈ z180K18M12ProfileOrders) :
    ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧
      frequencyOrder 180 (x - y) = z180K18M12RequiredOrder i := by
  by_contra hmissing
  have hcolorInj :
      Set.InjOn (z180K18M12MissingOrderColor i) (L : Set (ZMod 180)) := by
    intro x hx y hy hcolor
    by_contra hne
    have horderMissing :
        frequencyOrder 180 (x - y) ≠ z180K18M12RequiredOrder i := by
      intro horder
      apply hmissing
      exact ⟨x, hx, y, hy, hne, horder⟩
    have hsep := z180_k18_m12_missingOrderColor_separates
      i x y (hcontained x hx y hy hne) horderMissing hne
    exact hsep hcolor
  have hcardColors :
      (L.image (z180K18M12MissingOrderColor i)).card = 18 := by
    rw [Finset.card_image_iff.mpr hcolorInj, hcard]
  have hcolors : L.image (z180K18M12MissingOrderColor i) ⊆
      Finset.range (z180K18M12MissingOrderColorBound i) := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (z180_k18_m12_missingOrderColor_lt i z)
  have hle := Finset.card_le_card hcolors
  have hbound := z180_k18_m12_missingOrderColorBound_lt_eighteen i
  rw [hcardColors, Finset.card_range] at hle
  omega

/-- Inhabited exact clique-census interface for the `m = 12` branch. -/
theorem z180_k18_m12_cliqueCensus :
    Z180K18M12CliqueCensusInterface := by
  intro L hcard henv
  have hcontained := z180_k18_m12_profile_containment hcard henv
  refine ⟨hcontained, ?_⟩
  have h3 := z180_k18_m12_required_order_realized
    (0 : Fin 5) hcard hcontained
  have h9 := z180_k18_m12_required_order_realized
    (1 : Fin 5) hcard hcontained
  have h10 := z180_k18_m12_required_order_realized
    (2 : Fin 5) hcard hcontained
  have h30 := z180_k18_m12_required_order_realized
    (3 : Fin 5) hcard hcontained
  have h90 := z180_k18_m12_required_order_realized
    (4 : Fin 5) hcard hcontained
  intro q hq
  simp only [z180K18M12ProfileOrders, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · simpa [z180K18M12RequiredOrder] using h3
  · simpa [z180K18M12RequiredOrder] using h9
  · simpa [z180K18M12RequiredOrder] using h10
  · simpa [z180K18M12RequiredOrder] using h30
  · simpa [z180K18M12RequiredOrder] using h90

#print axioms z180_k18_m12_unwantedColor_separates
#print axioms z180_k18_m12_missingOrderColor_separates
#print axioms z180_k18_m12_profile_containment
#print axioms z180_k18_m12_cliqueCensus

end Fuglede
