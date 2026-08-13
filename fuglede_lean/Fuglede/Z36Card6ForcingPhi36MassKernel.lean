import Mathlib.Tactic

/-! Six-mass kernel for the cardinality-six `Phi_36` forcing lemma. -/

namespace Fuglede

theorem z36_phi36_allowed_mass_nonneg_ne_one (c : Int)
    (h : c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6) :
    0 ≤ c ∧ c ≠ 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> omega

theorem z36_phi36_block_masses_dichotomy
    (c0 c1 c2 c3 c4 c5 : Int)
    (h0 : c0 = 0 ∨ c0 = 2 ∨ c0 = 3 ∨ c0 = 4 ∨ c0 = 6)
    (h1 : c1 = 0 ∨ c1 = 2 ∨ c1 = 3 ∨ c1 = 4 ∨ c1 = 6)
    (h2 : c2 = 0 ∨ c2 = 2 ∨ c2 = 3 ∨ c2 = 4 ∨ c2 = 6)
    (h3 : c3 = 0 ∨ c3 = 2 ∨ c3 = 3 ∨ c3 = 4 ∨ c3 = 6)
    (h4 : c4 = 0 ∨ c4 = 2 ∨ c4 = 3 ∨ c4 = 4 ∨ c4 = 6)
    (h5 : c5 = 0 ∨ c5 = 2 ∨ c5 = 3 ∨ c5 = 4 ∨ c5 = 6)
    (hsum : c0 + c1 + c2 + c3 + c4 + c5 = 6) :
    (c0 ≠ 3 ∧ c1 ≠ 3 ∧ c2 ≠ 3 ∧ c3 ≠ 3 ∧ c4 ≠ 3 ∧ c5 ≠ 3) ∨
      ((c0 = 0 ∨ c0 = 3) ∧ (c1 = 0 ∨ c1 = 3) ∧
        (c2 = 0 ∨ c2 = 3) ∧ (c3 = 0 ∨ c3 = 3) ∧
        (c4 = 0 ∨ c4 = 3) ∧ (c5 = 0 ∨ c5 = 3)) := by
  obtain ⟨h0n, h0ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c0 h0
  obtain ⟨h1n, h1ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c1 h1
  obtain ⟨h2n, h2ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c2 h2
  obtain ⟨h3n, h3ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c3 h3
  obtain ⟨h4n, h4ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c4 h4
  obtain ⟨h5n, h5ne1⟩ := z36_phi36_allowed_mass_nonneg_ne_one c5 h5
  clear h0 h1 h2 h3 h4 h5
  by_cases hc0 : c0 = 3
  · right; omega
  by_cases hc1 : c1 = 3
  · right; omega
  by_cases hc2 : c2 = 3
  · right; omega
  by_cases hc3 : c3 = 3
  · right; omega
  by_cases hc4 : c4 = 3
  · right; omega
  by_cases hc5 : c5 = 3
  · right; omega
  · exact Or.inl ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩

#print axioms z36_phi36_allowed_mass_nonneg_ne_one
#print axioms z36_phi36_block_masses_dichotomy

end Fuglede
