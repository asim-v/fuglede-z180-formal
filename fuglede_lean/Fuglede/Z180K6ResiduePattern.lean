import Fuglede.Z180K6LowOrderArithmetic
import Fuglede.Z180K6SetNormalForm
import Fuglede.Z180K12Projection36Mask
import Mathlib.Tactic

/-!
# From the six-point normal form to projected residue counts

This module connects the geometric `Phi_30` defect normal form to the small
linear kernels used by the low-order sieve.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- The six coordinates in `Fin 36` lying over a prescribed residue modulo
six.  The explicit table keeps normalization predictable. -/
def z180Projection36ResidueSixIndices (r : ZMod 6) : Finset (Fin 36) :=
  match r.val with
  | 0 => {0, 6, 12, 18, 24, 30}
  | 1 => {1, 7, 13, 19, 25, 31}
  | 2 => {2, 8, 14, 20, 26, 32}
  | 3 => {3, 9, 15, 21, 27, 33}
  | 4 => {4, 10, 16, 22, 28, 34}
  | _ => {5, 11, 17, 23, 29, 35}

@[simp]
theorem mem_z180Projection36ResidueSixIndices_iff
    (r : ZMod 6) (i : Fin 36) :
    i ∈ z180Projection36ResidueSixIndices r ↔ (i.val : ZMod 6) = r := by
  exact (by decide : ∀ r : ZMod 6, ∀ i : Fin 36,
    i ∈ z180Projection36ResidueSixIndices r ↔ (i.val : ZMod 6) = r) r i

theorem sum_z180Projection36ResidueSixIndices
    (b : Fin 36 → Int) (r : ZMod 6) :
    (∑ i ∈ z180Projection36ResidueSixIndices r, b i) =
      z180K6ResidueSixSum b r := by
  unfold z180Projection36ResidueSixIndices z180K6ResidueSixSum
  split <;> simp_all <;> ring

private theorem z180Projection36Coordinate_cast_six (x : ZMod 180) :
    ((z180Projection36Coordinate x).val : ZMod 6) =
      (ZMod.cast x : ZMod 6) := by
  apply ZMod.val_injective
  change (z180Projection36Coordinate x).val % 6 = x.val % 6
  rw [z180Projection36Coordinate_val,
    Nat.mod_mod_of_dvd x.val (by norm_num : 6 ∣ 36)]

@[simp]
theorem z180Projection36Coordinate_mem_residueSixIndices_iff
    (x : ZMod 180) (r : ZMod 6) :
    z180Projection36Coordinate x ∈ z180Projection36ResidueSixIndices r ↔
      (ZMod.cast x : ZMod 6) = r := by
  rw [mem_z180Projection36ResidueSixIndices_iff,
    z180Projection36Coordinate_cast_six]

/-- Summing the projected occupancies over one class modulo six is exactly
the cardinality of the corresponding fibre of the original set. -/
theorem z180K6ResidueSixSum_occupancy_eq_filter_card
    (X : Finset (ZMod 180)) (r : ZMod 6) :
    z180K6ResidueSixSum
        (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) r =
      ((X.filter fun x => (ZMod.cast x : ZMod 6) = r).card : Int) := by
  classical
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter X
    (z180Projection36ResidueSixIndices r) z180Projection36Coordinate
  have hfilter :
      X.filter (fun x =>
        z180Projection36Coordinate x ∈
          z180Projection36ResidueSixIndices r) =
        X.filter (fun x => (ZMod.cast x : ZMod 6) = r) := by
    apply Finset.filter_congr
    intro x hx
    exact z180Projection36Coordinate_mem_residueSixIndices_iff x r
  rw [hfilter] at hpartition
  have hpartition' :
      (∑ i ∈ z180Projection36ResidueSixIndices r,
          z180Projection36Occupancy X i) =
        (X.filter fun x => (ZMod.cast x : ZMod 6) = r).card := by
    simpa only [z180Projection36Occupancy] using hpartition
  have hcast := congrArg (fun n : Nat => (n : Int)) hpartition'
  push_cast at hcast
  rw [sum_z180Projection36ResidueSixIndices] at hcast
  exact hcast

/-! The next lemma is deliberately independent of `ZMod 180`.  It packages
the only finite-set bookkeeping needed below: six distinct points with
values `(1,-1,0,0,0,0)` have fibre cardinalities `(4,1,0,0,0,1)` in
`ZMod 6`. -/
private theorem zero_residue_six_filter_cards
    {α : Type*} [DecidableEq α]
    (X : Finset α) (hcard : X.card = 6)
    (f : α → ZMod 6) (a b r1 r2 r3 r4 : α)
    (hsupport : X = {a, b, r1, r2, r3, r4})
    (ha : f a = 1) (hb : f b = -1)
    (hr1 : f r1 = 0) (hr2 : f r2 = 0)
    (hr3 : f r3 = 0) (hr4 : f r4 = 0) :
    (X.filter fun x => f x = 0).card = 4 ∧
    (X.filter fun x => f x = 1).card = 1 ∧
    (X.filter fun x => f x = 2).card = 0 ∧
    (X.filter fun x => f x = 3).card = 0 ∧
    (X.filter fun x => f x = 4).card = 0 ∧
    (X.filter fun x => f x = 5).card = 1 := by
  have hdistinct :
      a ∉ ({b, r1, r2, r3, r4} : Finset α) ∧
      b ∉ ({r1, r2, r3, r4} : Finset α) ∧
      r1 ∉ ({r2, r3, r4} : Finset α) ∧
      r2 ∉ ({r3, r4} : Finset α) ∧
      r3 ≠ r4 := by
    rw [hsupport] at hcard
    grind
  rcases hdistinct with ⟨ha_not, hb_not, hr1_not, hr2_not, hr3_ne⟩
  have hm1 : (-1 : ZMod 6) = 5 := by decide
  have hf0 : X.filter (fun x => f x = 0) = {r1, r2, r3, r4} := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxcast⟩
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp_all +decide
  have hf1 : X.filter (fun x => f x = 1) = {a} := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxcast⟩
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      subst x
      simp_all +decide
  have hf2 : X.filter (fun x => f x = 2) = ∅ := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty]
    constructor
    · intro hx
      rcases hx.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      contradiction
  have hf3 : X.filter (fun x => f x = 3) = ∅ := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty]
    constructor
    · intro hx
      rcases hx.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      contradiction
  have hf4 : X.filter (fun x => f x = 4) = ∅ := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty]
    constructor
    · intro hx
      rcases hx.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      contradiction
  have hf5 : X.filter (fun x => f x = 5) = {b} := by
    rw [hsupport]
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxcast⟩
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all +decide
    · intro hx
      subst x
      simp_all +decide
  rw [hf0, hf1, hf2, hf3, hf4, hf5]
  norm_num [hr1_not, hr2_not, hr3_ne]

private theorem zmod6_exhaustive (r : ZMod 6) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
  exact (by decide : ∀ r : ZMod 6,
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) r

private theorem z180K6ResidueSixPattern_of_oriented_support
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (a b r1 r2 r3 r4 : ZMod 180)
    (hsupport : X = {a, b, r1, r2, r3, r4})
    (hr2 : (ZMod.cast r2 : ZMod 6) = ZMod.cast r1)
    (hr3 : (ZMod.cast r3 : ZMod 6) = ZMod.cast r1)
    (hr4 : (ZMod.cast r4 : ZMod 6) = ZMod.cast r1)
    (ha : (ZMod.cast a : ZMod 6) = ZMod.cast r1 + 1)
    (hb : (ZMod.cast b : ZMod 6) = ZMod.cast r1 - 1) :
    Z180K6ResidueSixPattern
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) := by
  let B : Fin 36 → Int :=
    fun i => (z180Projection36Occupancy X i : Int)
  let c : ZMod 6 := ZMod.cast r1
  let f : ZMod 180 → ZMod 6 := fun x => ZMod.cast x - c
  have hfa : f a = 1 := by
    dsimp only [f, c]
    rw [ha]
    ring
  have hfb : f b = -1 := by
    dsimp only [f, c]
    rw [hb]
    ring
  have hfr1 : f r1 = 0 := by dsimp only [f, c]; ring
  have hfr2 : f r2 = 0 := by dsimp only [f, c]; rw [hr2]; ring
  have hfr3 : f r3 = 0 := by dsimp only [f, c]; rw [hr3]; ring
  have hfr4 : f r4 = 0 := by dsimp only [f, c]; rw [hr4]; ring
  have hstd := zero_residue_six_filter_cards X hcard f a b r1 r2 r3 r4
    hsupport hfa hfb hfr1 hfr2 hfr3 hfr4
  have hfilter (j r : ZMod 6) (hjr : j + c = r) :
      (X.filter fun x => (ZMod.cast x : ZMod 6) = r).card =
        (X.filter fun x => f x = j).card := by
    congr 1
    apply Finset.filter_congr
    intro x hx
    dsimp only [f]
    rw [sub_eq_iff_eq_add, hjr]
  have hs0 := z180K6ResidueSixSum_occupancy_eq_filter_card X (0 : ZMod 6)
  have hs1 := z180K6ResidueSixSum_occupancy_eq_filter_card X (1 : ZMod 6)
  have hs2 := z180K6ResidueSixSum_occupancy_eq_filter_card X (2 : ZMod 6)
  have hs3 := z180K6ResidueSixSum_occupancy_eq_filter_card X (3 : ZMod 6)
  have hs4 := z180K6ResidueSixSum_occupancy_eq_filter_card X (4 : ZMod 6)
  have hs5 := z180K6ResidueSixSum_occupancy_eq_filter_card X (5 : ZMod 6)
  change z180K6ResidueSixSum B 0 = _ at hs0
  change z180K6ResidueSixSum B 1 = _ at hs1
  change z180K6ResidueSixSum B 2 = _ at hs2
  change z180K6ResidueSixSum B 3 = _ at hs3
  change z180K6ResidueSixSum B 4 = _ at hs4
  change z180K6ResidueSixSum B 5 = _ at hs5
  rcases zmod6_exhaustive c with
    hc | hc | hc | hc | hc | hc
  · have hraw0 := (hfilter 0 0 (by simp +decide [hc])).trans hstd.1
    have hraw1 := (hfilter 1 1 (by simp +decide [hc])).trans hstd.2.1
    have hraw2 := (hfilter 2 2 (by simp +decide [hc])).trans hstd.2.2.1
    have hraw3 := (hfilter 3 3 (by simp +decide [hc])).trans hstd.2.2.2.1
    have hraw4 := (hfilter 4 4 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    have hraw5 := (hfilter 5 5 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inl ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩
  · have hraw0 := (hfilter 5 0 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    have hraw1 := (hfilter 0 1 (by simp +decide [hc])).trans hstd.1
    have hraw2 := (hfilter 1 2 (by simp +decide [hc])).trans hstd.2.1
    have hraw3 := (hfilter 2 3 (by simp +decide [hc])).trans hstd.2.2.1
    have hraw4 := (hfilter 3 4 (by simp +decide [hc])).trans hstd.2.2.2.1
    have hraw5 := (hfilter 4 5 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inr (Or.inl
      ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩)
  · have hraw0 := (hfilter 4 0 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    have hraw1 := (hfilter 5 1 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    have hraw2 := (hfilter 0 2 (by simp +decide [hc])).trans hstd.1
    have hraw3 := (hfilter 1 3 (by simp +decide [hc])).trans hstd.2.1
    have hraw4 := (hfilter 2 4 (by simp +decide [hc])).trans hstd.2.2.1
    have hraw5 := (hfilter 3 5 (by simp +decide [hc])).trans hstd.2.2.2.1
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inr (Or.inr (Or.inl
      ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩))
  · have hraw0 := (hfilter 3 0 (by simp +decide [hc])).trans hstd.2.2.2.1
    have hraw1 := (hfilter 4 1 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    have hraw2 := (hfilter 5 2 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    have hraw3 := (hfilter 0 3 (by simp +decide [hc])).trans hstd.1
    have hraw4 := (hfilter 1 4 (by simp +decide [hc])).trans hstd.2.1
    have hraw5 := (hfilter 2 5 (by simp +decide [hc])).trans hstd.2.2.1
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩)))
  · have hraw0 := (hfilter 2 0 (by simp +decide [hc])).trans hstd.2.2.1
    have hraw1 := (hfilter 3 1 (by simp +decide [hc])).trans hstd.2.2.2.1
    have hraw2 := (hfilter 4 2 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    have hraw3 := (hfilter 5 3 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    have hraw4 := (hfilter 0 4 (by simp +decide [hc])).trans hstd.1
    have hraw5 := (hfilter 1 5 (by simp +decide [hc])).trans hstd.2.1
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩))))
  · have hraw0 := (hfilter 1 0 (by simp +decide [hc])).trans hstd.2.1
    have hraw1 := (hfilter 2 1 (by simp +decide [hc])).trans hstd.2.2.1
    have hraw2 := (hfilter 3 2 (by simp +decide [hc])).trans hstd.2.2.2.1
    have hraw3 := (hfilter 4 3 (by simp +decide [hc])).trans hstd.2.2.2.2.1
    have hraw4 := (hfilter 5 4 (by simp +decide [hc])).trans hstd.2.2.2.2.2
    have hraw5 := (hfilter 0 5 (by simp +decide [hc])).trans hstd.1
    norm_num [hraw0, hraw1, hraw2, hraw3, hraw4, hraw5] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [Z180K6ResidueSixPattern]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩))))

/-- The genuine `Phi_30` defect normal form implies the integral `(4,1,1)`
pattern consumed by the low-order arithmetic kernels. -/
theorem z180_k6_projection_residue_pattern_of_phi30_defect
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    Z180K6ResidueSixPattern
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) := by
  obtain ⟨c, a, b, r1, r2, r3, r4, hab, hsupport, h0, h1, h2, h3, h4,
      hr12, hr13, hr14, hpair⟩ :=
    z180_card_six_phi30_defect_set_normal_form_with_support X hcard h30 h6
  rcases hpair with hp | hp
  · exact z180K6ResidueSixPattern_of_oriented_support X hcard
      a b r1 r2 r3 r4 hsupport hr12.symm hr13.symm hr14.symm
      (sub_eq_iff_eq_add'.mp hp.1)
      (by simpa [sub_eq_add_neg] using sub_eq_iff_eq_add'.mp hp.2)
  · exact z180K6ResidueSixPattern_of_oriented_support X hcard
      b a r1 r2 r3 r4 (by simpa [Finset.insert_comm] using hsupport)
      hr12.symm hr13.symm hr14.symm
      (sub_eq_iff_eq_add'.mp hp.2)
      (by simpa [sub_eq_add_neg] using sub_eq_iff_eq_add'.mp hp.1)

#print axioms z180K6ResidueSixSum_occupancy_eq_filter_card
#print axioms z180_k6_projection_residue_pattern_of_phi30_defect

end Fuglede
