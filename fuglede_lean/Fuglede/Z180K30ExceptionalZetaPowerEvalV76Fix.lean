import Fuglede.Z180K30ExceptionalCoeffInjectiveV71Fix3
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Exact evaluation of the K30 raw power table (V76 Fix)

This repaired shard proves that every hard-coded raw power-table entry is
the corresponding standard character of `ZMod 36`, and that all coefficient
folds used by the raw Gram certificate stay in the twelve-coordinate basis.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open Polynomial
open scoped BigOperators

noncomputable section

theorem zeta36V71Fix_pow_stdAddChar_v76Fix (n : Nat) :
    zeta36V71Fix ^ n = ZMod.stdAddChar (n : ZMod 36) := by
  unfold zeta36V71Fix
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp

theorem zetaPower_wf_v76Fix (exponent : Nat) :
    CoeffWF (zetaPower exponent) := by
  unfold CoeffWF zetaPower
  have hlt : exponent % 36 < 36 :=
    Nat.mod_lt exponent (by norm_num)
  interval_cases hq : exponent % 36 <;>
    simp [zetaPowerTable, hq]

private theorem foldl_coeffAdd_wf_v76Fix
    (values : List Coeff) (acc : Coeff)
    (hacc : CoeffWF acc)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    CoeffWF (values.foldl coeffAdd acc) := by
  induction values generalizing acc with
  | nil => simpa
  | cons head tail ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact coeffAdd_wf_v71Fix hacc (hvalues head (by simp))
      · intro c hc
        exact hvalues c (by simp [hc])

theorem coeffSum_wf_v76Fix
    (values : List Coeff)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    CoeffWF (coeffSum values) := by
  unfold coeffSum
  exact foldl_coeffAdd_wf_v76Fix
    values coeffZero coeffZero_wf_v71Fix hvalues

theorem energy_wf_v76Fix (V : RawSet) (difference : Nat) :
    CoeffWF (energy V difference) := by
  unfold energy
  apply coeffSum_wf_v76Fix
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨v, _hv, hc⟩
  rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
  exact zetaPower_wf_v76Fix _

theorem gramTraceSquare_wf_v76Fix (U V : RawSet) :
    CoeffWF (gramTraceSquare U V) := by
  unfold gramTraceSquare
  apply coeffSum_wf_v76Fix
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨u, _hu, hc⟩
  rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
  exact energy_wf_v76Fix V _

theorem gram_entry_wf_v76Fix
    {U V : RawSet} {c : Coeff} (hc : c ∈ gram U V) :
    CoeffWF c := by
  unfold gram at hc
  rcases List.mem_flatMap.mp hc with ⟨row, _hrow, hc⟩
  rcases List.mem_map.mp hc with ⟨column, _hcolumn, rfl⟩
  apply coeffSum_wf_v76Fix
  intro d hd
  rcases List.mem_map.mp hd with ⟨u, _hu, rfl⟩
  exact zetaPower_wf_v76Fix _

private theorem evalCoeffV71Fix_foldl_coeffAdd_v76Fix
    (values : List Coeff) (acc : Coeff)
    (hacc : CoeffWF acc)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    evalCoeffV71Fix (values.foldl coeffAdd acc) =
      evalCoeffV71Fix acc + (values.map evalCoeffV71Fix).sum := by
  induction values generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc := coeffAdd acc head)
        (coeffAdd_wf_v71Fix hacc (hvalues head (by simp)))]
      · rw [evalCoeffV71Fix_coeffAdd_v71Fix3
          hacc (hvalues head (by simp))]
        ac_rfl
      · intro c hc
        exact hvalues c (by simp [hc])

theorem evalCoeffV71Fix_coeffSum_v76Fix
    (values : List Coeff)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    evalCoeffV71Fix (coeffSum values) =
      (values.map evalCoeffV71Fix).sum := by
  unfold coeffSum
  simpa using
    (evalCoeffV71Fix_foldl_coeffAdd_v76Fix
      values coeffZero coeffZero_wf_v71Fix hvalues)

private theorem zeta36V71Fix_pow_six_relation_v76Fix :
    zeta36V71Fix ^ 12 = zeta36V71Fix ^ 6 - 1 := by
  have hprimitiveSix : IsPrimitiveRoot (zeta36V71Fix ^ 6) 6 := by
    convert IsPrimitiveRoot.pow_of_dvd
      zeta36V71Fix_isPrimitiveRoot (by norm_num : 6 ≠ 0)
        (by norm_num : 6 ∣ 36) using 1 <;> norm_num
  have hroot := hprimitiveSix.isRoot_cyclotomic (by norm_num : 0 < 6)
  have hrelation :
      (zeta36V71Fix ^ 6) ^ 2 - zeta36V71Fix ^ 6 + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.cyclotomic_six] using hroot
  calc
    zeta36V71Fix ^ 12 = (zeta36V71Fix ^ 6) ^ 2 := by ring
    _ = zeta36V71Fix ^ 6 - 1 := by linear_combination hrelation

private theorem zeta36V71Fix_pow_eighteen_v76Fix :
    zeta36V71Fix ^ 18 = -1 := by
  have hprimitiveTwo : IsPrimitiveRoot (zeta36V71Fix ^ 18) 2 := by
    convert IsPrimitiveRoot.pow_of_dvd
      zeta36V71Fix_isPrimitiveRoot (by norm_num : 18 ≠ 0)
        (by norm_num : 18 ∣ 36) using 1 <;> norm_num
  exact hprimitiveTwo.eq_neg_one_of_two_right

private theorem zeta36V71Fix_shift_twelve_v76Fix (i : Nat) :
    zeta36V71Fix ^ (i + 12) =
      -zeta36V71Fix ^ i + zeta36V71Fix ^ (i + 6) := by
  simp only [pow_add, zeta36V71Fix_pow_six_relation_v76Fix]
  ring

private theorem zeta36V71Fix_shift_eighteen_v76Fix (i : Nat) :
    zeta36V71Fix ^ (i + 18) = -zeta36V71Fix ^ i := by
  simp [pow_add, zeta36V71Fix_pow_eighteen_v76Fix]

private theorem zeta36V71Fix_pow_thirty_v76Fix :
    zeta36V71Fix ^ 30 = 1 - zeta36V71Fix ^ 6 := by
  calc
    zeta36V71Fix ^ 30 = zeta36V71Fix ^ 12 * zeta36V71Fix ^ 18 := by ring
    _ = 1 - zeta36V71Fix ^ 6 := by
      rw [zeta36V71Fix_pow_six_relation_v76Fix,
        zeta36V71Fix_pow_eighteen_v76Fix]
      ring

private theorem zeta36V71Fix_shift_thirty_v76Fix (i : Nat) :
    zeta36V71Fix ^ (i + 30) =
      zeta36V71Fix ^ i - zeta36V71Fix ^ (i + 6) := by
  simp only [pow_add, zeta36V71Fix_pow_thirty_v76Fix]
  ring

private theorem evalCoeffV71Fix_zetaPower_lt_twelve_v76Fix
    (q : Nat) (hq : q < 12) :
    evalCoeffV71Fix (zetaPower q) = zeta36V71Fix ^ q := by
  interval_cases q <;>
    norm_num [evalCoeffV71Fix, coeffPolynomialV71Fix, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeffV71Fix_zetaPower_twelve_eighteen_v76Fix
    (q : Nat) (hq12 : 12 ≤ q) (hq18 : q < 18) :
    evalCoeffV71Fix (zetaPower q) =
      -zeta36V71Fix ^ (q - 12) + zeta36V71Fix ^ (q - 6) := by
  interval_cases q <;>
    norm_num [evalCoeffV71Fix, coeffPolynomialV71Fix, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeffV71Fix_zetaPower_eighteen_thirty_v76Fix
    (q : Nat) (hq18 : 18 ≤ q) (hq30 : q < 30) :
    evalCoeffV71Fix (zetaPower q) = -zeta36V71Fix ^ (q - 18) := by
  interval_cases q <;>
    norm_num [evalCoeffV71Fix, coeffPolynomialV71Fix, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeffV71Fix_zetaPower_thirty_thirtySix_v76Fix
    (q : Nat) (hq30 : 30 ≤ q) (hq36 : q < 36) :
    evalCoeffV71Fix (zetaPower q) =
      zeta36V71Fix ^ (q - 30) - zeta36V71Fix ^ (q - 24) := by
  interval_cases q <;>
    norm_num [evalCoeffV71Fix, coeffPolynomialV71Fix, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ, sub_eq_add_neg]

theorem evalCoeffV71Fix_zetaPower_v76Fix (exponent : Nat) :
    evalCoeffV71Fix (zetaPower exponent) =
      ZMod.stdAddChar (exponent : ZMod 36) := by
  rw [← zeta36V71Fix_pow_stdAddChar_v76Fix exponent]
  have hpowMod :
      zeta36V71Fix ^ (exponent % 36) = zeta36V71Fix ^ exponent := by
    exact zeta36V71Fix_isPrimitiveRoot.eq_orderOf.symm ▸
      pow_mod_orderOf zeta36V71Fix exponent
  rw [← hpowMod]
  let q := exponent % 36
  have hq36 : q < 36 := Nat.mod_lt exponent (by norm_num)
  have hzetaPower : zetaPower exponent = zetaPower q := by
    unfold zetaPower
    simp [q, Nat.mod_eq_of_lt hq36]
  rw [hzetaPower]
  by_cases hq12 : q < 12
  · exact evalCoeffV71Fix_zetaPower_lt_twelve_v76Fix q hq12
  have hq12le : 12 ≤ q := Nat.le_of_not_gt hq12
  by_cases hq18 : q < 18
  · rw [evalCoeffV71Fix_zetaPower_twelve_eighteen_v76Fix
      q hq12le hq18]
    have hshift := zeta36V71Fix_shift_twelve_v76Fix (q - 12)
    have hq12' : q - 12 + 12 = q := Nat.sub_add_cancel hq12le
    have hq6 : q - 12 + 6 = q - 6 := by omega
    rw [hq12', hq6] at hshift
    exact hshift.symm
  have hq18le : 18 ≤ q := Nat.le_of_not_gt hq18
  by_cases hq30 : q < 30
  · rw [evalCoeffV71Fix_zetaPower_eighteen_thirty_v76Fix
      q hq18le hq30]
    have hshift := zeta36V71Fix_shift_eighteen_v76Fix (q - 18)
    have hq18' : q - 18 + 18 = q := Nat.sub_add_cancel hq18le
    rw [hq18'] at hshift
    exact hshift.symm
  have hq30le : 30 ≤ q := Nat.le_of_not_gt hq30
  rw [evalCoeffV71Fix_zetaPower_thirty_thirtySix_v76Fix
    q hq30le hq36]
  have hshift := zeta36V71Fix_shift_thirty_v76Fix (q - 30)
  have hq30' : q - 30 + 30 = q := Nat.sub_add_cancel hq30le
  have hq24 : q - 30 + 6 = q - 24 := by omega
  rw [hq30', hq24] at hshift
  exact hshift.symm

#print axioms zetaPower_wf_v76Fix
#print axioms evalCoeffV71Fix_coeffSum_v76Fix
#print axioms evalCoeffV71Fix_zetaPower_v76Fix
#print axioms gramTraceSquare_wf_v76Fix

end
end Fuglede.Z180K30ExceptionalRawV2
