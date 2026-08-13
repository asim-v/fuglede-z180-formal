import Fuglede.Z180K18LowOrderInterfaces
import Mathlib.Tactic

/-!
# Kernel-checked order-twenty exclusion for the `k = 18`, `m = 4` census

Canonical source: `fuglede_search/z180_k18_closure.py`

* source SHA-256:
  `3b8bb2943e5dfcae8e0439ae606b98d88c42da55b70384a651571274f1ca24b9`
* canonical common-neighbour payload SHA-256:
  `ec294c12e53612f027d67f64754685377a0a240f8d79d2e258006686bacff23a`

After translating an alleged order-twenty edge to `{0,d}`, each of the other
sixteen clique vertices must lie in the common-neighbour set below.  Direct
kernel reduction checks that this set has exactly eight points for each of
the eight possible elements `d` of order twenty.  The remaining argument is
only injectivity of translation and finite-set cardinality.

The computed proposition is defined independently from the Python payload:
it uses `frequencyOrder` and the envelope literal already consumed by the
formal interface.  A stale or incorrectly oriented payload therefore cannot
make the Lean theorem true.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Common neighbours of `0` and `d` in the exact `m = 4` envelope graph. -/
def z180K18M4HighEdgeCommonNeighbors (d : ZMod 180) : Finset (ZMod 180) :=
  Finset.univ.filter fun z =>
    z ≠ 0 ∧ z ≠ d ∧
      frequencyOrder 180 z ∈ z180K18M4EnvelopeOrders ∧
      frequencyOrder 180 (z - d) ∈ z180K18M4EnvelopeOrders

/-- The finite kernel certificate.  There are eight cases for `d`, and each
common-neighbour set has cardinality eight. -/
theorem z180_k18_m4_highEdgeCommonNeighbors_card
    : ∀ d : ZMod 180, frequencyOrder 180 d = 20 →
      (z180K18M4HighEdgeCommonNeighbors d).card = 8 := by
  decide

/-- A cardinality-eighteen clique in the `m = 4` envelope cannot contain an
order-twenty edge.  This is the inhabited census interface needed by the
terminal branch. -/
theorem z180_k18_m4_noHighEdgeCensus :
    Z180K18M4NoHighEdgeCensusInterface := by
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
  have hd0 : d ≠ 0 := by
    exact sub_ne_zero.mpr hne
  have hcardEraseZero : (K.erase 0).card = 17 := by
    rw [Finset.card_erase_of_mem hzeroK, hcardK]
  have hdEraseZero : d ∈ K.erase 0 :=
    Finset.mem_erase.mpr ⟨hd0, hdK⟩
  let S : Finset (ZMod 180) := (K.erase 0).erase d
  have hcardS : S.card = 16 := by
    change ((K.erase 0).erase d).card = 16
    rw [Finset.card_erase_of_mem hdEraseZero, hcardEraseZero]
  have hsubset : S ⊆ z180K18M4HighEdgeCommonNeighbors d := by
    intro z hz
    have hzd := (Finset.mem_erase.mp hz).1
    have hzEraseZero := (Finset.mem_erase.mp hz).2
    have hz0 := (Finset.mem_erase.mp hzEraseZero).1
    have hzK := (Finset.mem_erase.mp hzEraseZero).2
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hzK
    have huy : u ≠ y := by
      intro huy
      apply hz0
      rw [← huz, huy, sub_self]
    have hux : u ≠ x := by
      intro hux
      apply hzd
      rw [← huz, hux]
    have hzeroAllowed := henv u hu y hy huy
    have hdAllowed := henv u hu x hx hux
    rw [z180K18M4HighEdgeCommonNeighbors, Finset.mem_filter]
    refine ⟨Finset.mem_univ z, hz0, hzd, ?_, ?_⟩
    · simpa [huz] using hzeroAllowed
    · have heq : z - d = u - x := by
        rw [← huz]
        dsimp [d]
        abel
      rw [heq]
      exact hdAllowed
  have hle := Finset.card_le_card hsubset
  have hcommonCard : (z180K18M4HighEdgeCommonNeighbors d).card = 8 :=
    z180_k18_m4_highEdgeCommonNeighbors_card d (by simpa [d] using horder)
  rw [hcardS, hcommonCard] at hle
  omega

#print axioms z180_k18_m4_highEdgeCommonNeighbors_card
#print axioms z180_k18_m4_noHighEdgeCensus

end Fuglede
