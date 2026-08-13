import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Exact lower bounds for finite occupancy collision mass

For a finite family of occupancies `n i`, `collisionMass n` is the second moment
`∑ i, n i ^ 2`, regarded as an integer.  The main result in this file is the
sharp balanced lower bound: if `m` cells contain `m * u + r` objects, with
`r ≤ m`, then their collision mass is at least

`r * (u + 1)^2 + (m - r) * u^2`.

The proof uses the integral supporting line to the parabola between `u` and
`u + 1`; it does not require choosing or sorting the cells.
-/

namespace Fuglede

/-- The total number of objects represented by a finite occupancy function. -/
def occupancyMass {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  ∑ i, n i

/-- The ordered-pair collision mass (second moment) of a finite occupancy function. -/
def collisionMass {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℤ :=
  ∑ i, (n i : ℤ) ^ 2

@[simp] theorem occupancyMass_fin {m : ℕ} (n : Fin m → ℕ) :
    occupancyMass n = ∑ i, n i := rfl

@[simp] theorem collisionMass_fin {m : ℕ} (n : Fin m → ℕ) :
    collisionMass n = ∑ i, (n i : ℤ) ^ 2 := rfl

/-- The affine line through `u^2` and `(u+1)^2` lies below every integral square. -/
theorem square_supporting_line (u x : ℕ) :
    (2 * (u : ℤ) + 1) * (x : ℤ) - (u : ℤ) * ((u : ℤ) + 1) ≤ (x : ℤ) ^ 2 := by
  by_cases hxu : x ≤ u
  · have hxuz : (x : ℤ) ≤ (u : ℤ) := by exact_mod_cast hxu
    have h₁ : (x : ℤ) - (u : ℤ) ≤ 0 := sub_nonpos.mpr hxuz
    have h₂ : (x : ℤ) - (u : ℤ) - 1 ≤ 0 := by omega
    have hmul : 0 ≤ ((x : ℤ) - (u : ℤ)) * ((x : ℤ) - (u : ℤ) - 1) :=
      mul_nonneg_of_nonpos_of_nonpos h₁ h₂
    nlinarith
  · have hux : u + 1 ≤ x := by omega
    have huxZ : (u : ℤ) + 1 ≤ (x : ℤ) := by exact_mod_cast hux
    have h₁ : 0 ≤ (x : ℤ) - (u : ℤ) := by omega
    have h₂ : 0 ≤ (x : ℤ) - (u : ℤ) - 1 := by omega
    have hmul : 0 ≤ ((x : ℤ) - (u : ℤ)) * ((x : ℤ) - (u : ℤ) - 1) :=
      mul_nonneg h₁ h₂
    nlinarith

/-- Sharp lower bound for `m` occupancies with total mass `m*u+r`.

Equality is attained by taking `r` cells of occupancy `u+1` and the remaining
`m-r` cells of occupancy `u`.
-/
theorem collisionMass_lower_balanced {m u r : ℕ} (n : Fin m → ℕ)
    (hmass : occupancyMass n = m * u + r) (hr : r ≤ m) :
    (r : ℤ) * ((u : ℤ) + 1) ^ 2 + ((m : ℤ) - (r : ℤ)) * (u : ℤ) ^ 2 ≤
      collisionMass n := by
  have hpoint : ∀ i : Fin m,
      (2 * (u : ℤ) + 1) * (n i : ℤ) - (u : ℤ) * ((u : ℤ) + 1) ≤
        (n i : ℤ) ^ 2 := fun i ↦ square_supporting_line u (n i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  have hmassZ : (∑ i, (n i : ℤ)) = (m : ℤ) * (u : ℤ) + (r : ℤ) := by
    exact_mod_cast hmass
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hmassZ] at hsum
  simp only [collisionMass]
  have hrZ : (r : ℤ) ≤ (m : ℤ) := by exact_mod_cast hr
  nlinarith

/-- A simple capacity upper bound.  The sharper quotient/remainder form is a
future refinement; this lemma is already enough whenever only a linear cap on
the collision mass is needed. -/
theorem collisionMass_le_capacity_mul_mass {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (c : ℕ) (hcap : ∀ i, n i ≤ c) :
    collisionMass n ≤ (c : ℤ) * (occupancyMass n : ℤ) := by
  have hpoint : ∀ i : ι, (n i : ℤ) ^ 2 ≤ (c : ℤ) * (n i : ℤ) := by
    intro i
    have hnonneg : (0 : ℤ) ≤ n i := by positivity
    have hle : (n i : ℤ) ≤ c := by exact_mod_cast hcap i
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  rw [← Finset.mul_sum] at hsum
  simpa only [collisionMass, occupancyMass, Nat.cast_sum] using hsum

/-- The largest collision mass possible for total mass `k` when every cell has
capacity `c`: fill `k / c` cells completely and one cell with the remainder. -/
def capacityEnergy (c k : ℕ) : ℕ :=
  (k / c) * c ^ 2 + (k % c) ^ 2

/-- Combining two capped occupancy blocks cannot decrease their extremal energy. -/
theorem capacityEnergy_superadditive {c : ℕ} (hc : 0 < c) (a b : ℕ) :
    capacityEnergy c a + capacityEnergy c b ≤ capacityEnergy c (a + b) := by
  by_cases hrem : a % c + b % c < c
  · rw [capacityEnergy, capacityEnergy, capacityEnergy,
      Nat.add_div_eq_of_add_mod_lt hrem, Nat.add_mod_of_add_mod_lt hrem]
    have hnonneg : 0 ≤ (a % c) * (b % c) := Nat.zero_le _
    nlinarith
  · have hcarry : c ≤ a % c + b % c := by omega
    have hdiv := Nat.add_div_eq_of_le_mod_add_mod hcarry hc
    have hmod := Nat.add_mod_add_of_le_add_mod hcarry
    rw [capacityEnergy, capacityEnergy, capacityEnergy, hdiv]
    have ha : a % c < c := Nat.mod_lt a hc
    have hb : b % c < c := Nat.mod_lt b hc
    have hca : c - a % c + a % c = c := by omega
    have hcb : c - b % c + b % c = c := by omega
    have hnonneg : 0 ≤ (c - a % c) * (c - b % c) := Nat.zero_le _
    nlinarith

/-- Below one capacity block, `capacityEnergy` is just the square. -/
theorem capacityEnergy_eq_sq_of_le {c x : ℕ} (hc : 0 < c) (hx : x ≤ c) :
    capacityEnergy c x = x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hlt
  · rw [capacityEnergy, Nat.div_self hc, Nat.mod_self]
    simp
  · simp [capacityEnergy, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-- Superadditivity iterated over any finite family. -/
theorem sum_capacityEnergy_le_finset {ι : Type*} (s : Finset ι)
    (c : ℕ) (hc : 0 < c) (n : ι → ℕ) :
    (∑ i ∈ s, capacityEnergy c (n i)) ≤ capacityEnergy c (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [capacityEnergy]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (Nat.add_le_add_left ih _).trans (capacityEnergy_superadditive hc _ _)

/-- `sum_capacityEnergy_le_finset` over all indices of a finite type. -/
theorem sum_capacityEnergy_le {ι : Type*} [Fintype ι] (c : ℕ) (hc : 0 < c)
    (n : ι → ℕ) :
    (∑ i, capacityEnergy c (n i)) ≤ capacityEnergy c (∑ i, n i) := by
  simpa using sum_capacityEnergy_le_finset (Finset.univ : Finset ι) c hc n

/-- Exact quotient/remainder capacity bound for finite occupancies. -/
theorem collisionMass_le_capacityEnergy {ι : Type*} [Fintype ι]
    (n : ι → ℕ) {c : ℕ} (hc : 0 < c) (hcap : ∀ i, n i ≤ c) :
    collisionMass n ≤ (capacityEnergy c (occupancyMass n) : ℤ) := by
  have hsquares : (∑ i, n i ^ 2) = ∑ i, capacityEnergy c (n i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (capacityEnergy_eq_sq_of_le hc (hcap i)).symm
  have hnat : (∑ i, n i ^ 2) ≤ capacityEnergy c (∑ i, n i) := by
    rw [hsquares]
    exact sum_capacityEnergy_le c hc n
  calc
    collisionMass n = ((∑ i, n i ^ 2 : ℕ) : ℤ) := by simp [collisionMass]
    _ ≤ (capacityEnergy c (∑ i, n i) : ℤ) := by exact_mod_cast hnat
    _ = (capacityEnergy c (occupancyMass n) : ℤ) := by rfl

/-- Sharp upper bound in the explicit decomposition `k = c*v+s`, `s<c`. -/
theorem collisionMass_upper_capacity {ι : Type*} [Fintype ι]
    (n : ι → ℕ) {c v s : ℕ} (hc : 0 < c) (hs : s < c)
    (hcap : ∀ i, n i ≤ c) (hmass : occupancyMass n = c * v + s) :
    collisionMass n ≤ (v : ℤ) * (c : ℤ) ^ 2 + (s : ℤ) ^ 2 := by
  have h := collisionMass_le_capacityEnergy n hc hcap
  rw [hmass] at h
  have he : capacityEnergy c (c * v + s) = v * c ^ 2 + s ^ 2 := by
    simp [capacityEnergy, Nat.mul_add_div hc,
      Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs]
  rw [he] at h
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using h

end Fuglede
