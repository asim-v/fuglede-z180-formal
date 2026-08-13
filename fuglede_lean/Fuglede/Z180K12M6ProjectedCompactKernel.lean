import Fuglede.Z180K12M6Order36FibreTable
import Mathlib.Tactic

/-!
# Compact Presburger kernels for the projected cardinality-twelve sieve

The order `9`, `18`, and `36` projected exclusions admit much smaller
arithmetic interfaces than the original 36-indicator DPLL certificates.
This file contains only those compact integer kernels.  Set- and
mask-polynomial adapters live in separate modules.
-/

namespace Fuglede

set_option maxHeartbeats 500000

theorem z180_k12_m6_five_multiplier_bounds
    (k : Int) (hlo : -12 ≤ 5 * k) (hhi : 5 * k ≤ 12) :
    -2 ≤ k ∧ k ≤ 2 := by
  omega

private theorem z180_k12_order36_fibre_realization
    (E O z : Int)
    (hElo : 0 ≤ E) (hEhi : E ≤ 3)
    (hOlo : 0 ≤ O) (hOhi : O ≤ 3)
    (hD : E - O = 3 * z) :
    ∃ f : Z180K12Order36Fibre, f.even = E ∧ f.odd = O := by
  have hcases :
      (E = 0 ∧ O = 0) ∨
      (E = 1 ∧ O = 1) ∨
      (E = 2 ∧ O = 2) ∨
      (E = 3 ∧ O = 3) ∨
      (E = 3 ∧ O = 0) ∨
      (E = 0 ∧ O = 3) := by
    omega
  rcases hcases with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.zero, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.balancedOne, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.balancedTwo, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.balancedThree, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.positive, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨.negative, rfl, rfl⟩

/-- Order 36: each of the six residue-class fibres has even/odd counts
`Eᵣ,Oᵣ` in `[0,3]`.  The cyclotomic equations make their difference three
times an integer `zᵣ` in `[-1,1]`.  Four counts of size three then exclude a
nonzero `Phi₆` remainder divisible by five. -/
theorem z180_k12_m6_order36_compact_impossible
    (E0 O0 E1 O1 E2 O2 E3 O3 E4 O4 E5 O5 : Int)
    (z0 z1 z2 z3 z4 z5 k0 k1 : Int)
    (hE0lo : 0 ≤ E0) (hE0hi : E0 ≤ 3)
    (hO0lo : 0 ≤ O0) (hO0hi : O0 ≤ 3)
    (hE1lo : 0 ≤ E1) (hE1hi : E1 ≤ 3)
    (hO1lo : 0 ≤ O1) (hO1hi : O1 ≤ 3)
    (hE2lo : 0 ≤ E2) (hE2hi : E2 ≤ 3)
    (hO2lo : 0 ≤ O2) (hO2hi : O2 ≤ 3)
    (hE3lo : 0 ≤ E3) (hE3hi : E3 ≤ 3)
    (hO3lo : 0 ≤ O3) (hO3hi : O3 ≤ 3)
    (hE4lo : 0 ≤ E4) (hE4hi : E4 ≤ 3)
    (hO4lo : 0 ≤ O4) (hO4hi : O4 ≤ 3)
    (hE5lo : 0 ≤ E5) (hE5hi : E5 ≤ 3)
    (hO5lo : 0 ≤ O5) (hO5hi : O5 ≤ 3)
    (hD0 : E0 - O0 = 3 * z0)
    (hD1 : E1 - O1 = 3 * z1)
    (hD2 : E2 - O2 = 3 * z2)
    (hD3 : E3 - O3 = 3 * z3)
    (hD4 : E4 - O4 = 3 * z4)
    (hD5 : E5 - O5 = 3 * z5)
    (hmod4_0 : E0 + O2 + E4 = 3)
    (hmod4_1 : E1 + O3 + E5 = 3)
    (hmod4_2 : O0 + E2 + O4 = 3)
    (hmod4_3 : O1 + E3 + O5 = 3)
    (hphi6_0 :
      (E0 + O0) - (E2 + O2) - (E3 + O3) + (E5 + O5) = 5 * k0)
    (hphi6_1 :
      (E1 + O1) + (E2 + O2) - (E4 + O4) - (E5 + O5) = 5 * k1)
    (hphi6_ne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  obtain ⟨f0, hf0E, hf0O⟩ := z180_k12_order36_fibre_realization
    E0 O0 z0 hE0lo hE0hi hO0lo hO0hi hD0
  obtain ⟨f1, hf1E, hf1O⟩ := z180_k12_order36_fibre_realization
    E1 O1 z1 hE1lo hE1hi hO1lo hO1hi hD1
  obtain ⟨f2, hf2E, hf2O⟩ := z180_k12_order36_fibre_realization
    E2 O2 z2 hE2lo hE2hi hO2lo hO2hi hD2
  obtain ⟨f3, hf3E, hf3O⟩ := z180_k12_order36_fibre_realization
    E3 O3 z3 hE3lo hE3hi hO3lo hO3hi hD3
  obtain ⟨f4, hf4E, hf4O⟩ := z180_k12_order36_fibre_realization
    E4 O4 z4 hE4lo hE4hi hO4lo hO4hi hD4
  obtain ⟨f5, hf5E, hf5O⟩ := z180_k12_order36_fibre_realization
    E5 O5 z5 hE5lo hE5hi hO5lo hO5hi hD5
  have hfive0 :
      ((f0.even + f0.odd) - (f2.even + f2.odd) -
        (f3.even + f3.odd) + (f5.even + f5.odd)) % 5 = 0 := by
    rw [hf0E, hf0O, hf2E, hf2O, hf3E, hf3O, hf5E, hf5O]
    rw [hphi6_0]
    simp
  have hfive1 :
      ((f1.even + f1.odd) + (f2.even + f2.odd) -
        (f4.even + f4.odd) - (f5.even + f5.odd)) % 5 = 0 := by
    rw [hf1E, hf1O, hf2E, hf2O, hf4E, hf4O, hf5E, hf5O]
    rw [hphi6_1]
    simp
  have htable := z180_k12_order36_fibre_table f0 f1 f2 f3 f4 f5
  unfold Z180K12Order36TableProperty at htable
  have hmod0 : f0.even + f2.odd + f4.even = 3 := by
    rw [hf0E, hf2O, hf4E]
    exact hmod4_0
  have hmod1 : f1.even + f3.odd + f5.even = 3 := by
    rw [hf1E, hf3O, hf5E]
    exact hmod4_1
  have hmod2 : f0.odd + f2.even + f4.odd = 3 := by
    rw [hf0O, hf2E, hf4O]
    exact hmod4_2
  have hmod3 : f1.odd + f3.even + f5.odd = 3 := by
    rw [hf1O, hf3E, hf5O]
    exact hmod4_3
  obtain ⟨hzero0, hzero1⟩ :=
    htable hmod0 hmod1 hmod2 hmod3 hfive0 hfive1
  rw [hf0E, hf0O, hf2E, hf2O, hf3E, hf3O, hf5E, hf5O] at hzero0
  rw [hf1E, hf1O, hf2E, hf2O, hf4E, hf4O, hf5E, hf5O] at hzero1
  have hk0 : 5 * k0 = 0 := hphi6_0.symm.trans hzero0
  have hk1 : 5 * k1 = 0 := hphi6_1.symm.trans hzero1
  exact hphi6_ne.elim (fun h ↦ h hk0) (fun h ↦ h hk1)

/-- Order 18: the three cyclotomic fibres have imbalance `3*zᵣ`.
The two `Phi₆` coordinates are therefore divisible by three, while the
cardinality bound confines their quotients by five to `[-2,2]`. -/
theorem z180_k12_m6_order18_compact_impossible
    (z0 z1 z2 k0 k1 : Int)
    (hk0lo : -2 ≤ k0) (hk0hi : k0 ≤ 2)
    (hk1lo : -2 ≤ k1) (hk1hi : k1 ≤ 2)
    (hphi6_0 : 3 * (z0 - z2) = 5 * k0)
    (hphi6_1 : 3 * (z1 + z2) = 5 * k1)
    (hphi6_ne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  omega

private theorem z180_k12_m6_order9_imbalance_impossible
    (D0 D1 D2 k0 k1 : Int)
    (hD0lo : -6 ≤ D0) (hD0hi : D0 ≤ 6)
    (hD1lo : -6 ≤ D1) (hD1hi : D1 ≤ 6)
    (hD2lo : -6 ≤ D2) (hD2hi : D2 ≤ 6)
    (hD0p : D0 ≠ 5) (hD0m : D0 ≠ -5)
    (hD1p : D1 ≠ 5) (hD1m : D1 ≠ -5)
    (hD2p : D2 ≠ 5) (hD2m : D2 ≠ -5)
    (hsum : D0 + D1 + D2 = 0)
    (hphi6_0 : D0 - D2 = 5 * k0)
    (hphi6_1 : -D1 + D2 = 5 * k1)
    (hphi6_ne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  omega

/-- Order 9: write `Eᵣ,Oᵣ` for the two parity counts in each residue class
modulo three.  A primitive ninth-root zero says their total is `3*nᵣ`.
The two parity halves each contain six points.  These small margin equations
exclude every nonzero `Phi₆` remainder divisible by five. -/
theorem z180_k12_m6_order9_compact_impossible
    (E0 O0 E1 O1 E2 O2 n0 n1 n2 k0 k1 : Int)
    (hE0lo : 0 ≤ E0) (hE0hi : E0 ≤ 6)
    (hO0lo : 0 ≤ O0) (hO0hi : O0 ≤ 6)
    (hE1lo : 0 ≤ E1) (hE1hi : E1 ≤ 6)
    (hO1lo : 0 ≤ O1) (hO1hi : O1 ≤ 6)
    (hE2lo : 0 ≤ E2) (hE2hi : E2 ≤ 6)
    (hO2lo : 0 ≤ O2) (hO2hi : O2 ≤ 6)
    (hclass0 : E0 + O0 = 3 * n0)
    (hclass1 : E1 + O1 = 3 * n1)
    (hclass2 : E2 + O2 = 3 * n2)
    (heven : E0 + E1 + E2 = 6)
    (hodd : O0 + O1 + O2 = 6)
    (hphi6_0 : E0 - O0 - E2 + O2 = 5 * k0)
    (hphi6_1 : -E1 + O1 + E2 - O2 = 5 * k1)
    (hphi6_ne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  let D0 := E0 - O0
  let D1 := E1 - O1
  let D2 := E2 - O2
  have hD0lo : -6 ≤ D0 := by omega
  have hD0hi : D0 ≤ 6 := by omega
  have hD1lo : -6 ≤ D1 := by omega
  have hD1hi : D1 ≤ 6 := by omega
  have hD2lo : -6 ≤ D2 := by omega
  have hD2hi : D2 ≤ 6 := by omega
  have hD0p : D0 ≠ 5 := by
    intro h
    omega
  have hD0m : D0 ≠ -5 := by
    intro h
    omega
  have hD1p : D1 ≠ 5 := by
    intro h
    omega
  have hD1m : D1 ≠ -5 := by
    intro h
    omega
  have hD2p : D2 ≠ 5 := by
    intro h
    omega
  have hD2m : D2 ≠ -5 := by
    intro h
    omega
  have hsum : D0 + D1 + D2 = 0 := by omega
  exact z180_k12_m6_order9_imbalance_impossible
    D0 D1 D2 k0 k1
    hD0lo hD0hi hD1lo hD1hi hD2lo hD2hi
    hD0p hD0m hD1p hD1m hD2p hD2m hsum
    (by omega) (by omega) hphi6_ne

#print axioms z180_k12_m6_order36_compact_impossible
#print axioms z180_k12_m6_order18_compact_impossible
#print axioms z180_k12_m6_order9_compact_impossible

end Fuglede
