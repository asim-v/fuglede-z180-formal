import Fuglede.CRT2310
import Fuglede.FrequencyOrder
import Fuglede.InnerDistribution
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# CRT support and exact character order at modulus `2310`

For the square-free modulus `2310 = 2 * 3 * 5 * 7 * 11`, the additive
order of a residue is exactly the product of the prime CRT coordinates on
which it is nonzero.  This identifies the support language used by the
multi-axis argument with the cyclotomic index used by the certificates.
-/

namespace Fuglede

/-- Product of the prime moduli indexed by a CRT support. -/
def supportModulus (D : Finset (Fin 5)) : ℕ :=
  ∏ i ∈ D, crt2310Modulus i

@[simp]
theorem supportModulus_empty : supportModulus ∅ = 1 := by
  simp [supportModulus]

@[simp]
theorem supportModulus_univ : supportModulus Finset.univ = 2310 := by
  simp only [supportModulus]
  exact crt2310Modulus_prod

theorem crt2310Modulus_prime (i : Fin 5) :
    Nat.Prime (crt2310Modulus i) := by
  fin_cases i <;> norm_num [crt2310Modulus]

/-- Enlarging a support can only multiply its modulus by further factors. -/
theorem supportModulus_dvd_of_subset {D E : Finset (Fin 5)} (hDE : D ⊆ E) :
    supportModulus D ∣ supportModulus E := by
  unfold supportModulus
  exact Finset.prod_dvd_prod_of_subset D E crt2310Modulus hDE

theorem supportModulus_dvd_2310 (D : Finset (Fin 5)) :
    supportModulus D ∣ 2310 := by
  rw [← supportModulus_univ]
  exact supportModulus_dvd_of_subset (Finset.subset_univ D)

/-- Every difference support has at most the five available prime axes. -/
theorem card_differenceSupport_le_five (x y : ZMod 2310) :
    (differenceSupport x y).card ≤ 5 := by
  exact card_crt2310Support_le_five (x - y)

/-- A nonzero coordinate in `ZMod p`, for one of the five CRT primes, has
additive order exactly `p`; a zero coordinate has order one. -/
theorem addOrderOf_crt2310_coordinate (d : ZMod 2310) (i : Fin 5) :
    addOrderOf (toCRT2310 d i) =
      if i ∈ crt2310Support d then crt2310Modulus i else 1 := by
  classical
  by_cases hi : i ∈ crt2310Support d
  · have hne : toCRT2310 d i ≠ 0 := mem_crt2310Support.mp hi
    rw [if_pos hi]
    letI : Fact (Nat.Prime (crt2310Modulus i)) :=
      ⟨crt2310Modulus_prime i⟩
    apply addOrderOf_eq_prime
    · rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    · exact hne
  · have hz : toCRT2310 d i = 0 := by
      simpa [mem_crt2310Support] using hi
    rw [if_neg hi, hz]
    simp

/-- Removing the coordinates outside `D`, whose contribution is `1`, does
not change the least common multiple. -/
theorem lcm_indicator_eq_lcm (D : Finset (Fin 5)) :
    Finset.univ.lcm
        (fun i => if i ∈ D then crt2310Modulus i else 1) =
      D.lcm crt2310Modulus := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i hi
    by_cases hD : i ∈ D
    · simpa [hD] using
        (Finset.dvd_lcm (s := D) (f := crt2310Modulus) hD)
    · simp [hD]
  · apply Finset.lcm_dvd
    intro i hi
    have hmem : i ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ i
    have hdvd := Finset.dvd_lcm
      (s := (Finset.univ : Finset (Fin 5)))
      (f := fun j => if j ∈ D then crt2310Modulus j else 1) hmem
    simpa [hi] using hdvd

/-- Since the five CRT moduli are pairwise coprime, their lcm over a support
is their product. -/
theorem support_lcm_eq_supportModulus (D : Finset (Fin 5)) :
    D.lcm crt2310Modulus = supportModulus D := by
  unfold supportModulus
  apply Finset.lcm_eq_prod
  intro i hi j hj hij
  exact crt2310Modulus_pairwise hij

/-- The cyclotomic frequency index of `d` is the product of exactly those
CRT primes on which `d` is nonzero. -/
theorem frequencyOrder_eq_supportModulus (d : ZMod 2310) :
    frequencyOrder 2310 d = supportModulus (crt2310Support d) := by
  calc
    frequencyOrder 2310 d = addOrderOf d :=
      frequencyOrder_2310_eq_addOrderOf d
    _ = addOrderOf (toCRT2310 d) :=
      (crt2310AddEquiv.addOrderOf_eq d).symm
    _ = Finset.univ.lcm (fun i => addOrderOf (toCRT2310 d i)) :=
      Pi.addOrderOf (toCRT2310 d)
    _ = Finset.univ.lcm
          (fun i => if i ∈ crt2310Support d then crt2310Modulus i else 1) := by
      apply Finset.lcm_congr rfl
      intro i hi
      exact addOrderOf_crt2310_coordinate d i
    _ = (crt2310Support d).lcm crt2310Modulus :=
      lcm_indicator_eq_lcm (crt2310Support d)
    _ = supportModulus (crt2310Support d) :=
      support_lcm_eq_supportModulus (crt2310Support d)

/-- Raw CRT-support formulation for a difference. -/
theorem frequencyOrder_sub_eq_crtSupportModulus (x y : ZMod 2310) :
    frequencyOrder 2310 (x - y) =
      supportModulus (crt2310Support (x - y)) :=
  frequencyOrder_eq_supportModulus (x - y)

/-- Difference-support formulation used directly by the inner-distribution
and projection arguments. -/
theorem frequencyOrder_sub_eq_supportModulus (x y : ZMod 2310) :
    frequencyOrder 2310 (x - y) = supportModulus (differenceSupport x y) := by
  simpa [differenceSupport] using
    frequencyOrder_sub_eq_crtSupportModulus x y

end Fuglede
