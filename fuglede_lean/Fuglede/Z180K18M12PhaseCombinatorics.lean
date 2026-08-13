import Fuglede.Z180K18M12PhaseOrientation
import Fuglede.Z180FiveLevelFourier
import Mathlib.Tactic

/-!
# Singleton-level and selected-mass combinatorics for `k = 18`, `m = 12`

The `Phi_60`/not-`Phi_12` defect makes all five fifth-coordinate levels
nonempty.  Nine pair indices distributed among those five levels therefore
have a singleton level.  Independently, the pair phases have residues
`0,1,2` modulo three with multiplicities `3,3,3`; after a common phase shift,
the eight selected phase classes contain exactly six pair indices.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

/-- Base frequency `15`, of exact order twelve and with zero fifth CRT
coordinate. -/
noncomputable def z180K18M12OrderTwelveBaseFrequency : CRT180 :=
  toCRT180 (15 : ZMod 180)

@[simp]
theorem z180K18M12OrderTwelveBaseFrequency_fifthCoord :
    crt180FifthCoord z180K18M12OrderTwelveBaseFrequency = 0 := by
  change (ZMod.cast (15 : ZMod 180) : ZMod 5) = 0
  decide

@[simp]
theorem z180K18M12OrderTwelveBaseFrequency_order :
    frequencyOrder 180
      (fromCRT180 z180K18M12OrderTwelveBaseFrequency) = 12 := by
  rw [z180K18M12OrderTwelveBaseFrequency, fromCRT180_toCRT180]
  decide

theorem sum_zmod_five_explicit_phase
    {R : Type*} [AddCommMonoid R] (f : ZMod 5 → R) :
    (∑ c : ZMod 5, f c) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert
    (by decide : (0 : ZMod 5) ∉ ({1, 2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (1 : ZMod 5) ∉ ({2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (2 : ZMod 5) ∉ ({3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (3 : ZMod 5) ∉ ({4} : Finset (ZMod 5)))]
  simp [add_assoc]

/-- A genuine order-twelve defect makes every pair level nonempty. -/
theorem z180_k18_m12_pairLevels_nonempty_of_defect
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A) :
    ∀ c : ZMod 5, (z180K18M12PairLevelFiber p c).Nonempty := by
  have hpoints := z180FiveLevelsNonempty_of_cyclotomic_defect
    A z180K18M12OrderTwelveBaseFrequency 12
      z180K18M12OrderTwelveBaseFrequency_fifthCoord
      z180K18M12OrderTwelveBaseFrequency_order (by simpa using h60) h12
  intro c
  obtain ⟨x, hx, hxc⟩ := hpoints c
  obtain ⟨r, hr⟩ := p.cover hx
  refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩⟩
  have hcast : (ZMod.cast x : ZMod 5) = c :=
    (crt180FifthCoord_toCRT180 x).symm.trans hxc
  rcases hr with rfl | rfl
  · exact (p.first_level r).symm.trans hcast
  · exact (p.second_level r).symm.trans hcast

/-- The five pair-level cardinalities sum to the nine pair indices. -/
theorem sum_z180K18M12PairLevelFiber_card
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) :
    (∑ c : ZMod 5, (z180K18M12PairLevelFiber p c).card) = 9 := by
  classical
  simpa [z180K18M12PairLevelFiber] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (ZMod 9))
      (Finset.univ : Finset (ZMod 5)) p.level)

/-- Nine pair indices meeting five levels always have a singleton level. -/
theorem z180_k18_m12_exists_singleton_pairLevel_of_defect
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A) :
    ∃ c : ZMod 5, ∃ r : ZMod 9,
      z180K18M12PairLevelFiber p c = {r} := by
  have hnonempty := z180_k18_m12_pairLevels_nonempty_of_defect p h60 h12
  have hsum := sum_z180K18M12PairLevelFiber_card p
  rw [sum_zmod_five_explicit_phase] at hsum
  have h0pos := Finset.card_pos.mpr (hnonempty 0)
  have h1pos := Finset.card_pos.mpr (hnonempty 1)
  have h2pos := Finset.card_pos.mpr (hnonempty 2)
  have h3pos := Finset.card_pos.mpr (hnonempty 3)
  have h4pos := Finset.card_pos.mpr (hnonempty 4)
  have hone :
      (z180K18M12PairLevelFiber p 0).card = 1 ∨
      (z180K18M12PairLevelFiber p 1).card = 1 ∨
      (z180K18M12PairLevelFiber p 2).card = 1 ∨
      (z180K18M12PairLevelFiber p 3).card = 1 ∨
      (z180K18M12PairLevelFiber p 4).card = 1 := by
    omega
  rcases hone with h | h | h | h | h
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    exact ⟨0, r, hr⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    exact ⟨1, r, hr⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    exact ⟨2, r, hr⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    exact ⟨3, r, hr⟩
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    exact ⟨4, r, hr⟩

private theorem zmod9_shifted_selected_card (t : ZMod 3) :
    ((Finset.univ : Finset (ZMod 9)).filter fun r =>
      (ZMod.cast r : ZMod 3) - t ≠ 2).card = 6 := by
  fin_cases t <;> decide

/-- A common phase shift preserves the aggregate selected mass six. -/
theorem z180_k18_m12_selected_normalized_pairPhases_card
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) :
    ((Finset.univ : Finset (ZMod 9)).filter fun r =>
      z180K18M12NormalizedPairPhase p shift r ∈
        z180K18M12SelectedPhases).card = 6 := by
  have h := zmod9_shifted_selected_card (ZMod.cast shift : ZMod 3)
  have hfilter :
      ((Finset.univ : Finset (ZMod 9)).filter fun r =>
        z180K18M12NormalizedPairPhase p shift r ∈
          z180K18M12SelectedPhases) =
      ((Finset.univ : Finset (ZMod 9)).filter fun r =>
        (ZMod.cast r : ZMod 3) - ZMod.cast shift ≠ 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_z180K18M12SelectedPhases_iff,
      z180K18M12NormalizedPairPhase_cast_three]
  rw [hfilter]
  exact h

/-- In one fixed fifth level, the sum of the eight selected phase counts is
the number of selected pair indices in that level. -/
theorem z180_k18_m12_selected_count_eq_filter_card
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) :
    z180K18M12NormalizedPhaseCount p shift c 0 +
      z180K18M12NormalizedPhaseCount p shift c 1 +
      z180K18M12NormalizedPhaseCount p shift c 3 +
      z180K18M12NormalizedPhaseCount p shift c 4 +
      z180K18M12NormalizedPhaseCount p shift c 6 +
      z180K18M12NormalizedPhaseCount p shift c 7 +
      z180K18M12NormalizedPhaseCount p shift c 9 +
      z180K18M12NormalizedPhaseCount p shift c 10 =
        ((((z180K18M12PairLevelFiber p c).filter fun r =>
          z180K18M12NormalizedPairPhase p shift r ∈
            z180K18M12SelectedPhases).card : Nat) : Int) := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (z180K18M12PairLevelFiber p c) z180K18M12SelectedPhases
      (z180K18M12NormalizedPairPhase p shift)
  have hcast := congrArg (fun n : Nat => (n : Int)) h
  push_cast at hcast
  norm_num [z180K18M12SelectedPhases, z180K18M12NormalizedPhaseCount,
    z180K18M12NormalizedPhaseFiber, add_assoc] at hcast ⊢
  exact hcast

/-- Summing the eight selected phase counts over all five levels gives six. -/
theorem z180_k18_m12_selected_phaseCounts_sum
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) :
    (∑ c : ZMod 5,
      (z180K18M12NormalizedPhaseCount p shift c 0 +
       z180K18M12NormalizedPhaseCount p shift c 1 +
       z180K18M12NormalizedPhaseCount p shift c 3 +
       z180K18M12NormalizedPhaseCount p shift c 4 +
       z180K18M12NormalizedPhaseCount p shift c 6 +
       z180K18M12NormalizedPhaseCount p shift c 7 +
       z180K18M12NormalizedPhaseCount p shift c 9 +
       z180K18M12NormalizedPhaseCount p shift c 10)) = 6 := by
  classical
  have hlevels := Finset.sum_card_fiberwise_eq_card_filter
    ((Finset.univ : Finset (ZMod 9)).filter fun r =>
      z180K18M12NormalizedPairPhase p shift r ∈
        z180K18M12SelectedPhases)
    (Finset.univ : Finset (ZMod 5)) p.level
  have hlevelsCast := congrArg (fun n : Nat => (n : Int)) hlevels
  push_cast at hlevelsCast
  have hselected := z180_k18_m12_selected_normalized_pairPhases_card p shift
  have hselectedInt :
      ((((Finset.univ : Finset (ZMod 9)).filter fun r =>
        z180K18M12NormalizedPairPhase p shift r ∈
          z180K18M12SelectedPhases).card : Nat) : Int) = 6 := by
    exact_mod_cast hselected
  simp only [Finset.mem_univ, Finset.filter_true] at hlevelsCast
  rw [hselectedInt] at hlevelsCast
  calc
    _ = ∑ c : ZMod 5,
        ((((z180K18M12PairLevelFiber p c).filter fun r =>
          z180K18M12NormalizedPairPhase p shift r ∈
            z180K18M12SelectedPhases).card : Nat) : Int) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact z180_k18_m12_selected_count_eq_filter_card p shift c
    _ = 6 := by
      simpa [z180K18M12PairLevelFiber, Finset.filter_filter,
        and_left_comm, and_comm, and_assoc] using hlevelsCast

#print axioms z180_k18_m12_pairLevels_nonempty_of_defect
#print axioms z180_k18_m12_exists_singleton_pairLevel_of_defect
#print axioms z180_k18_m12_selected_phaseCounts_sum

end Fuglede
