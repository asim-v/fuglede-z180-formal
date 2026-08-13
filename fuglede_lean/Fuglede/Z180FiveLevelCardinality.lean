import Fuglede.Z180FiveLevelFourier
import Mathlib.Tactic

/-!
# Cardinal profiles of the five `ZMod 5` fibres

This is the elementary counting half of the `Phi_30` defect normal form.  A
six-point set meeting all five fifth-coordinate fibres has one fibre of size
two and four fibres of size one.
-/

namespace Fuglede

open scoped BigOperators

/-- Cardinality of one residue fibre modulo five. -/
noncomputable def z180FifthFiberCard
    (X : Finset (ZMod 180)) (c : ZMod 5) : Nat :=
  (X.filter fun x ↦ crt180FifthCoord (toCRT180 x) = c).card

/-- The five fibre cardinalities sum to the set cardinality. -/
theorem sum_z180FifthFiberCard (X : Finset (ZMod 180)) :
    (∑ c : ZMod 5, z180FifthFiberCard X c) = X.card := by
  classical
  simpa [z180FifthFiberCard] using
    (Finset.sum_card_fiberwise_eq_card_filter X
      (Finset.univ : Finset (ZMod 5))
      (fun x ↦ crt180FifthCoord (toCRT180 x)))

/-- A witnessed fibre is nonempty. -/
theorem z180FifthFiberCard_pos_of_exists
    (X : Finset (ZMod 180)) (c : ZMod 5)
    (h : ∃ x ∈ X, (ZMod.cast x : ZMod 5) = c) :
    0 < z180FifthFiberCard X c := by
  obtain ⟨x, hx, hxc⟩ := h
  apply Finset.card_pos.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨hx,
    (crt180FifthCoord_toCRT180 x).trans hxc⟩⟩

/-- Explicit five-way profile.  This form is convenient for later finite
normalisation without any choice of a preferred residue. -/
theorem z180_card_six_fifthFiber_profile_cases
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (hnonempty : ∀ c : ZMod 5,
      ∃ x ∈ X, (ZMod.cast x : ZMod 5) = c) :
    (z180FifthFiberCard X 0 = 2 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 2 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 2 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 2 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 2) := by
  have hsum := sum_z180FifthFiberCard X
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by
    decide
  rw [huniv] at hsum
  rw [Finset.sum_insert
    (by decide : (0 : ZMod 5) ∉ ({1, 2, 3, 4} : Finset (ZMod 5)))] at hsum
  rw [Finset.sum_insert
    (by decide : (1 : ZMod 5) ∉ ({2, 3, 4} : Finset (ZMod 5)))] at hsum
  rw [Finset.sum_insert
    (by decide : (2 : ZMod 5) ∉ ({3, 4} : Finset (ZMod 5)))] at hsum
  rw [Finset.sum_insert
    (by decide : (3 : ZMod 5) ∉ ({4} : Finset (ZMod 5)))] at hsum
  simp only [Finset.sum_singleton] at hsum
  rw [hcard] at hsum
  have h0 := z180FifthFiberCard_pos_of_exists X 0 (hnonempty 0)
  have h1 := z180FifthFiberCard_pos_of_exists X 1 (hnonempty 1)
  have h2 := z180FifthFiberCard_pos_of_exists X 2 (hnonempty 2)
  have h3 := z180FifthFiberCard_pos_of_exists X 3 (hnonempty 3)
  have h4 := z180FifthFiberCard_pos_of_exists X 4 (hnonempty 4)
  omega

/-- Coordinate-free version of the same profile: there is one double fibre
and every other fibre is a singleton. -/
theorem z180_card_six_fifthFiber_unique_double
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (hnonempty : ∀ c : ZMod 5,
      ∃ x ∈ X, (ZMod.cast x : ZMod 5) = c) :
    ∃ cDouble : ZMod 5,
      z180FifthFiberCard X cDouble = 2 ∧
      ∀ c : ZMod 5, c ≠ cDouble → z180FifthFiberCard X c = 1 := by
  rcases z180_card_six_fifthFiber_profile_cases X hcard hnonempty with
      h | h | h | h | h
  · refine ⟨0, h.1, ?_⟩
    intro c hc
    fin_cases c
    · exact (hc rfl).elim
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · refine ⟨1, h.2.1, ?_⟩
    intro c hc
    fin_cases c
    · exact h.1
    · exact (hc rfl).elim
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · refine ⟨2, h.2.2.1, ?_⟩
    intro c hc
    fin_cases c
    · exact h.1
    · exact h.2.1
    · exact (hc rfl).elim
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · refine ⟨3, h.2.2.2.1, ?_⟩
    intro c hc
    fin_cases c
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact (hc rfl).elim
    · exact h.2.2.2.2
  · refine ⟨4, h.2.2.2.2, ?_⟩
    intro c hc
    fin_cases c
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact (hc rfl).elim

/-- The `Phi_30`/not-`Phi_6` defect therefore forces the `(2,1,1,1,1)`
profile at cardinality six. -/
theorem z180_card_six_phi30_defect_fifthFiber_profile_cases
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    (z180FifthFiberCard X 0 = 2 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 2 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 2 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 2 ∧
      z180FifthFiberCard X 4 = 1) ∨
    (z180FifthFiberCard X 0 = 1 ∧
      z180FifthFiberCard X 1 = 1 ∧
      z180FifthFiberCard X 2 = 1 ∧
      z180FifthFiberCard X 3 = 1 ∧
      z180FifthFiberCard X 4 = 2) :=
  z180_card_six_fifthFiber_profile_cases X hcard
    (z180_phi30_defect_fiveLevels_nonempty X h30 h6)

/-- Coordinate-free defect profile. -/
theorem z180_card_six_phi30_defect_fifthFiber_unique_double
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    ∃ cDouble : ZMod 5,
      z180FifthFiberCard X cDouble = 2 ∧
      ∀ c : ZMod 5, c ≠ cDouble → z180FifthFiberCard X c = 1 :=
  z180_card_six_fifthFiber_unique_double X hcard
    (z180_phi30_defect_fiveLevels_nonempty X h30 h6)

end Fuglede
