import Fuglede.CRT180
import Fuglede.ExactOrderEnergy
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# Exact-order frequencies under the `4 x 9 x 5` CRT decomposition

For a divisor `e` of `180`, the exact additive-order orbit in `ZMod 180`
is the Cartesian product of the exact-order orbits in its three CRT
coordinates.  The local order is the prime-power part `gcd e m_i`, where
`m_i` is respectively `4`, `9`, or `5`.

This module is deliberately independent of the character-sum computation
in `CRT180Ramanujan`: it supplies only the finite group/order reindexing.
-/

namespace Fuglede

open scoped BigOperators

/-- The part of an exact order belonging to one prime-power CRT coordinate. -/
def crt180OrderPart (e : ℕ) (i : Fin 3) : ℕ :=
  Nat.gcd e (crt180Modulus i)

/-- CRT frequency vectors whose image in `ZMod 180` has additive order `e`. -/
noncomputable def exactCRTFrequencies180 (e : ℕ) : Finset CRT180 :=
  Finset.univ.filter fun d ↦ frequencyOrder 180 (fromCRT180 d) = e

@[simp]
theorem mem_exactCRTFrequencies180 {e : ℕ} {d : CRT180} :
    d ∈ exactCRTFrequencies180 e ↔
      frequencyOrder 180 (fromCRT180 d) = e := by
  simp [exactCRTFrequencies180]

/-- The order of a CRT vector is the lcm of the orders of its coordinates. -/
theorem frequencyOrder_fromCRT180_eq_lcm (d : CRT180) :
    frequencyOrder 180 (fromCRT180 d) =
      Finset.univ.lcm
        (fun i ↦ frequencyOrder (crt180Modulus i) (d i)) := by
  calc
    frequencyOrder 180 (fromCRT180 d) = addOrderOf (fromCRT180 d) :=
      frequencyOrder_eq_addOrderOf (by norm_num) _
    _ = addOrderOf d := by
      rw [← crt180AddEquiv.addOrderOf_eq (fromCRT180 d)]
      simp [fromCRT180]
    _ = Finset.univ.lcm (fun i ↦ addOrderOf (d i)) :=
      Pi.addOrderOf d
    _ = Finset.univ.lcm
        (fun i ↦ frequencyOrder (crt180Modulus i) (d i)) := by
      apply Finset.lcm_congr rfl
      intro i hi
      exact (frequencyOrder_eq_addOrderOf
        (crt180Modulus_neZero i).out (d i)).symm

private theorem local_frequencyOrders_pairwise (d : CRT180) :
    Set.Pairwise (Finset.univ : Finset (Fin 3))
      (fun i j ↦ Nat.Coprime
        (frequencyOrder (crt180Modulus i) (d i))
        (frequencyOrder (crt180Modulus j) (d j))) := by
  intro i hi j hj hij
  apply Nat.Coprime.of_dvd
    (frequencyOrder_dvd_modulus (d i))
    (frequencyOrder_dvd_modulus (d j))
  exact crt180Modulus_pairwise hij

/-- Since the coordinate moduli are pairwise coprime, the global order is
the product, rather than merely the lcm, of the three local orders. -/
theorem frequencyOrder_fromCRT180_eq_prod (d : CRT180) :
    frequencyOrder 180 (fromCRT180 d) =
      ∏ i, frequencyOrder (crt180Modulus i) (d i) := by
  rw [frequencyOrder_fromCRT180_eq_lcm]
  exact Finset.lcm_eq_prod (local_frequencyOrders_pairwise d)

private theorem gcd_product_parts
    {a b c : ℕ}
    (ha : a ∣ 4) (hb : b ∣ 9) (hc : c ∣ 5)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) :
    Nat.gcd (a * b * c) 4 = a ∧
      Nat.gcd (a * b * c) 9 = b ∧
      Nat.gcd (a * b * c) 5 = c := by
  have ha4 : a ≤ 4 := Nat.le_of_dvd (by norm_num) ha
  have hb9 : b ≤ 9 := Nat.le_of_dvd (by norm_num) hb
  have hc5 : c ≤ 5 := Nat.le_of_dvd (by norm_num) hc
  interval_cases a
  all_goals interval_cases b
  all_goals interval_cases c
  all_goals norm_num at ha
  all_goals norm_num at hb
  all_goals norm_num at hc
  all_goals norm_num

private theorem prod_crt180OrderPart_eq_of_mem_divisors
    {e : ℕ} (he : e ∈ (180).divisors) :
    (∏ i, crt180OrderPart e i) = e := by
  have he_dvd : e ∣ 180 := (Nat.mem_divisors.mp he).1
  have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he_dvd (by norm_num)
  have he_le : e ≤ 180 := Nat.le_of_dvd (by norm_num) he_dvd
  interval_cases e
  all_goals norm_num at he_dvd
  all_goals
    norm_num [crt180OrderPart, crt180Modulus, Fin.prod_univ_succ]

private theorem local_order_eq_crt180OrderPart_of_global
    {d : CRT180} {e : ℕ}
    (hglobal : frequencyOrder 180 (fromCRT180 d) = e) (i : Fin 3) :
    frequencyOrder (crt180Modulus i) (d i) = crt180OrderPart e i := by
  let a := frequencyOrder 4 (d 0)
  let b := frequencyOrder 9 (d 1)
  let c := frequencyOrder 5 (d 2)
  have ha : a ∣ 4 := frequencyOrder_dvd_modulus (d 0)
  have hb : b ∣ 9 := frequencyOrder_dvd_modulus (d 1)
  have hc : c ∣ 5 := frequencyOrder_dvd_modulus (d 2)
  have ha0 : 0 < a := by
    dsimp [a]
    rw [frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  have hb0 : 0 < b := by
    dsimp [b]
    rw [frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  have hc0 : 0 < c := by
    dsimp [c]
    rw [frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  have hprod : a * b * c = e := by
    rw [← hglobal, frequencyOrder_fromCRT180_eq_prod]
    simp [a, b, c, crt180Modulus, Fin.prod_univ_succ, Nat.mul_assoc]
  have hgcd := gcd_product_parts ha hb hc ha0 hb0 hc0
  rw [← hprod]
  fin_cases i <;>
    simp [crt180OrderPart, crt180Modulus, a, b, c] at hgcd ⊢
  · exact hgcd.1.symm
  · exact hgcd.2.1.symm
  · exact hgcd.2.2.symm

/-- For a divisor `e` of `180`, global exact order `e` is equivalent to
having local exact orders `gcd e 4`, `gcd e 9`, and `gcd e 5`. -/
theorem frequencyOrder_fromCRT180_eq_iff_local
    {d : CRT180} {e : ℕ} (he : e ∈ (180).divisors) :
    frequencyOrder 180 (fromCRT180 d) = e ↔
      ∀ i, frequencyOrder (crt180Modulus i) (d i) =
        crt180OrderPart e i := by
  constructor
  · intro hglobal i
    exact local_order_eq_crt180OrderPart_of_global hglobal i
  · intro hlocal
    rw [frequencyOrder_fromCRT180_eq_prod]
    calc
      (∏ i, frequencyOrder (crt180Modulus i) (d i)) =
          ∏ i, crt180OrderPart e i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hlocal i
      _ = e := prod_crt180OrderPart_eq_of_mem_divisors he

/-- The global exact-order CRT orbit factors as the Cartesian product of
the three local exact-order orbits. -/
theorem exactCRTFrequencies180_eq_piFinset
    {e : ℕ} (he : e ∈ (180).divisors) :
    exactCRTFrequencies180 e =
      Fintype.piFinset (fun i ↦
        exactOrderFrequencies (N := crt180Modulus i)
          (crt180OrderPart e i)) := by
  classical
  ext d
  rw [mem_exactCRTFrequencies180, Fintype.mem_piFinset]
  simpa only [mem_exactOrderFrequencies] using
    frequencyOrder_fromCRT180_eq_iff_local (d := d) he

/-- Reindexing the CRT orbit through the inverse CRT equivalence recovers
the ordinary exact-order orbit in `ZMod 180`. -/
theorem map_exactCRTFrequencies180_fromCRT180 (e : ℕ) :
    (exactCRTFrequencies180 e).map
        crt180AddEquiv.symm.toEquiv.toEmbedding =
      exactOrderFrequencies (N := 180) e := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact mem_exactOrderFrequencies.mpr
      (mem_exactCRTFrequencies180.mp hd)
  · intro hx
    have horder : frequencyOrder 180 x = e :=
      mem_exactOrderFrequencies.mp hx
    rw [Finset.mem_map]
    refine ⟨toCRT180 x, ?_, ?_⟩
    · exact mem_exactCRTFrequencies180.mpr (by simpa using horder)
    · exact fromCRT180_toCRT180 x

end Fuglede
