import Fuglede.Z180K6PhaseGeometry
import Mathlib.Tactic

/-!
# Set-level normal form for the `Phi_30` defect at cardinality six

This module connects the five-fibre cardinality profile with the exact phase
geometry.  It extracts the two points in the unique double fibre and the four
singleton points, proves that the singleton base residues agree modulo six,
and proves that the double residues are exactly `+1` and `-1` around them.
-/

namespace Fuglede

/-- The fifth-coordinate fibre of a subset of `ZMod 180`. -/
noncomputable def z180FifthFiber (X : Finset (ZMod 180)) (c : ZMod 5) :
    Finset (ZMod 180) :=
  X.filter fun x ↦ crt180FifthCoord (toCRT180 x) = c

@[simp]
theorem card_z180FifthFiber (X : Finset (ZMod 180)) (c : ZMod 5) :
    (z180FifthFiber X c).card = z180FifthFiberCard X c := rfl

/-- A fibre of cardinality one has an explicit unique representative. -/
theorem z180FifthFiber_exists_singleton_of_card_one
    (X : Finset (ZMod 180)) (c : ZMod 5)
    (hcard : z180FifthFiberCard X c = 1) :
    ∃ r : ZMod 180, z180FifthFiber X c = {r} := by
  apply Finset.card_eq_one.mp
  simpa [card_z180FifthFiber] using hcard

/-- A fibre of cardinality two has two distinct explicit representatives. -/
theorem z180FifthFiber_exists_pair_of_card_two
    (X : Finset (ZMod 180)) (c : ZMod 5)
    (hcard : z180FifthFiberCard X c = 2) :
    ∃ a b : ZMod 180, a ≠ b ∧ z180FifthFiber X c = {a, b} := by
  apply Finset.card_eq_two.mp
  simpa [card_z180FifthFiber] using hcard

/-- The CRT pairing at the concrete base frequency is the ordinary phase at
frequency `30`. -/
theorem z180_orderSixBase_pairing_eq_phase (x : ZMod 180) :
    z180StandardCRTCharacterPairing (toCRT180 x)
        z180OrderSixBaseFrequency =
      ZMod.stdAddChar (x * 30) := by
  simp [z180StandardCRTCharacterPairing, z180OrderSixBaseFrequency,
    mul_comm]

/-- A singleton fifth fibre contributes its single order-six phase. -/
theorem z180FiveLevelFourierSum_eq_phase_of_singleton
    (X : Finset (ZMod 180)) (c : ZMod 5) (r : ZMod 180)
    (hfiber : z180FifthFiber X c = {r}) :
    z180FiveLevelFourierSum X z180OrderSixBaseFrequency c =
      ZMod.stdAddChar (r * 30) := by
  have hfiber' :
      X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c) = {r} := by
    exact hfiber
  rw [z180FiveLevelFourierSum, hfiber']
  simp [z180_orderSixBase_pairing_eq_phase]

/-- A double fifth fibre contributes the sum of its two order-six phases. -/
theorem z180FiveLevelFourierSum_eq_phase_sum_of_pair
    (X : Finset (ZMod 180)) (c : ZMod 5) (a b : ZMod 180)
    (hab : a ≠ b) (hfiber : z180FifthFiber X c = {a, b}) :
    z180FiveLevelFourierSum X z180OrderSixBaseFrequency c =
      ZMod.stdAddChar (a * 30) + ZMod.stdAddChar (b * 30) := by
  have hfiber' :
      X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c) = {a, b} := by
    exact hfiber
  rw [z180FiveLevelFourierSum, hfiber']
  simp [hab, z180_orderSixBase_pairing_eq_phase]

/-- Equal singleton level sums force equal base residues modulo six. -/
theorem z180_phi30_singleton_residues_eq
    (X : Finset (ZMod 180))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    {c c' : ZMod 5} {r r' : ZMod 180}
    (hr : z180FifthFiber X c = {r})
    (hr' : z180FifthFiber X c' = {r'}) :
    (ZMod.cast r : ZMod 6) = ZMod.cast r' := by
  have heq := z180_phi30_defect_fiveLevelSums_eq X h30 c c'
  rw [z180FiveLevelFourierSum_eq_phase_of_singleton X c r hr,
    z180FiveLevelFourierSum_eq_phase_of_singleton X c' r' hr'] at heq
  exact z180_cast_six_eq_of_order_six_phase_eq heq

/-- Comparing the double level with a singleton level gives the exact
`(+1,-1)` residue pattern modulo six. -/
theorem z180_phi30_double_residues_normal_form
    (X : Finset (ZMod 180))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    {cDouble cSingle : ZMod 5} {a b r : ZMod 180}
    (hab : a ≠ b) (hpair : z180FifthFiber X cDouble = {a, b})
    (hsingle : z180FifthFiber X cSingle = {r}) :
    (((ZMod.cast a : ZMod 6) - ZMod.cast r = 1 ∧
        (ZMod.cast b : ZMod 6) - ZMod.cast r = -1) ∨
      ((ZMod.cast a : ZMod 6) - ZMod.cast r = -1 ∧
        (ZMod.cast b : ZMod 6) - ZMod.cast r = 1)) := by
  have heq := z180_phi30_defect_fiveLevelSums_eq X h30 cDouble cSingle
  rw [z180FiveLevelFourierSum_eq_phase_sum_of_pair X cDouble a b hab hpair,
    z180FiveLevelFourierSum_eq_phase_of_singleton X cSingle r hsingle] at heq
  exact z180_cast_six_pair_normal_form_of_phase_sum heq

private theorem zmod5_add_one_ne_self (c : ZMod 5) : c + 1 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_two_ne_self (c : ZMod 5) : c + 2 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_three_ne_self (c : ZMod 5) : c + 3 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_four_ne_self (c : ZMod 5) : c + 4 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_cycle_exhaustive (c q : ZMod 5) :
    q = c ∨ q = c + 1 ∨ q = c + 2 ∨ q = c + 3 ∨ q = c + 4 := by
  exact (by decide : ∀ c q : ZMod 5,
    q = c ∨ q = c + 1 ∨ q = c + 2 ∨ q = c + 3 ∨ q = c + 4) c q

/-- Five explicit fibre equalities recover the whole six-point set. -/
theorem z180_eq_six_points_of_fifthFibers
    (X : Finset (ZMod 180)) (c : ZMod 5)
    (a b r1 r2 r3 r4 : ZMod 180)
    (h0 : z180FifthFiber X c = {a, b})
    (h1 : z180FifthFiber X (c + 1) = {r1})
    (h2 : z180FifthFiber X (c + 2) = {r2})
    (h3 : z180FifthFiber X (c + 3) = {r3})
    (h4 : z180FifthFiber X (c + 4) = {r4}) :
    X = {a, b, r1, r2, r3, r4} := by
  classical
  have haX : a ∈ X := by
    have : a ∈ z180FifthFiber X c := by rw [h0]; simp
    exact (Finset.mem_filter.mp this).1
  have hbX : b ∈ X := by
    have : b ∈ z180FifthFiber X c := by rw [h0]; simp
    exact (Finset.mem_filter.mp this).1
  have hr1X : r1 ∈ X := by
    have : r1 ∈ z180FifthFiber X (c + 1) := by rw [h1]; simp
    exact (Finset.mem_filter.mp this).1
  have hr2X : r2 ∈ X := by
    have : r2 ∈ z180FifthFiber X (c + 2) := by rw [h2]; simp
    exact (Finset.mem_filter.mp this).1
  have hr3X : r3 ∈ X := by
    have : r3 ∈ z180FifthFiber X (c + 3) := by rw [h3]; simp
    exact (Finset.mem_filter.mp this).1
  have hr4X : r4 ∈ X := by
    have : r4 ∈ z180FifthFiber X (c + 4) := by rw [h4]; simp
    exact (Finset.mem_filter.mp this).1
  apply Finset.Subset.antisymm
  · intro x hx
    have hmem (q : ZMod 5)
        (hq : crt180FifthCoord (toCRT180 x) = q) :
        x ∈ z180FifthFiber X q := by
      exact Finset.mem_filter.mpr ⟨hx, hq⟩
    rcases zmod5_cycle_exhaustive c
        (crt180FifthCoord (toCRT180 x)) with
      hq | hq | hq | hq | hq
    · have := hmem c hq
      rw [h0] at this
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases Finset.mem_insert.mp this with hxa | hxb
      · exact Or.inl hxa
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp hxb))
    · have := hmem (c + 1) hq
      rw [h1] at this
      simp_all
    · have := hmem (c + 2) hq
      rw [h2] at this
      simp_all
    · have := hmem (c + 3) hq
      rw [h3] at this
      simp_all
    · have := hmem (c + 4) hq
      rw [h4] at this
      simp_all
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact haX
    · exact hbX
    · exact hr1X
    · exact hr2X
    · exact hr3X
    · exact hr4X

/-- Complete set-level normal form of the `Phi_30`/not-`Phi_6` branch.  The
unique double fibre is followed cyclically by four singleton fibres.  Their
base residues agree modulo six, while the double residues are the two adjacent
classes around that common singleton residue. -/
theorem z180_card_six_phi30_defect_set_normal_form
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    ∃ (cDouble : ZMod 5) (a b r1 r2 r3 r4 : ZMod 180),
      a ≠ b ∧
      z180FifthFiber X cDouble = {a, b} ∧
      z180FifthFiber X (cDouble + 1) = {r1} ∧
      z180FifthFiber X (cDouble + 2) = {r2} ∧
      z180FifthFiber X (cDouble + 3) = {r3} ∧
      z180FifthFiber X (cDouble + 4) = {r4} ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r2 ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r3 ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r4 ∧
      ((((ZMod.cast a : ZMod 6) - ZMod.cast r1 = 1 ∧
          (ZMod.cast b : ZMod 6) - ZMod.cast r1 = -1) ∨
        ((ZMod.cast a : ZMod 6) - ZMod.cast r1 = -1 ∧
          (ZMod.cast b : ZMod 6) - ZMod.cast r1 = 1))) := by
  obtain ⟨cDouble, hdouble, hsingle⟩ :=
    z180_card_six_phi30_defect_fifthFiber_unique_double X hcard h30 h6
  obtain ⟨a, b, hab, hp⟩ :=
    z180FifthFiber_exists_pair_of_card_two X cDouble hdouble
  obtain ⟨r1, hr1⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (cDouble + 1) (hsingle _ (zmod5_add_one_ne_self cDouble))
  obtain ⟨r2, hr2⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (cDouble + 2) (hsingle _ (zmod5_add_two_ne_self cDouble))
  obtain ⟨r3, hr3⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (cDouble + 3) (hsingle _ (zmod5_add_three_ne_self cDouble))
  obtain ⟨r4, hr4⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (cDouble + 4) (hsingle _ (zmod5_add_four_ne_self cDouble))
  refine ⟨cDouble, a, b, r1, r2, r3, r4, hab, hp, hr1, hr2, hr3,
    hr4, ?_, ?_, ?_, ?_⟩
  · exact z180_phi30_singleton_residues_eq X h30 hr1 hr2
  · exact z180_phi30_singleton_residues_eq X h30 hr1 hr3
  · exact z180_phi30_singleton_residues_eq X h30 hr1 hr4
  · exact z180_phi30_double_residues_normal_form X h30 hab hp hr1

/-- The same normal form with the explicit equality recovering the whole
support. -/
theorem z180_card_six_phi30_defect_set_normal_form_with_support
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    ∃ (cDouble : ZMod 5) (a b r1 r2 r3 r4 : ZMod 180),
      a ≠ b ∧
      X = {a, b, r1, r2, r3, r4} ∧
      z180FifthFiber X cDouble = {a, b} ∧
      z180FifthFiber X (cDouble + 1) = {r1} ∧
      z180FifthFiber X (cDouble + 2) = {r2} ∧
      z180FifthFiber X (cDouble + 3) = {r3} ∧
      z180FifthFiber X (cDouble + 4) = {r4} ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r2 ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r3 ∧
      (ZMod.cast r1 : ZMod 6) = ZMod.cast r4 ∧
      ((((ZMod.cast a : ZMod 6) - ZMod.cast r1 = 1 ∧
          (ZMod.cast b : ZMod 6) - ZMod.cast r1 = -1) ∨
        ((ZMod.cast a : ZMod 6) - ZMod.cast r1 = -1 ∧
          (ZMod.cast b : ZMod 6) - ZMod.cast r1 = 1))) := by
  obtain ⟨c, a, b, r1, r2, r3, r4, hab, h0, h1, h2, h3, h4,
      hr12, hr13, hr14, hpair⟩ :=
    z180_card_six_phi30_defect_set_normal_form X hcard h30 h6
  exact ⟨c, a, b, r1, r2, r3, r4, hab,
    z180_eq_six_points_of_fifthFibers X c a b r1 r2 r3 r4 h0 h1 h2 h3 h4,
    h0, h1, h2, h3, h4, hr12, hr13, hr14, hpair⟩

end Fuglede
