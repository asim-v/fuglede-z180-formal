import Fuglede.Z180K30ExceptionalRawCoreV2
import Fuglede.SpectralFourier
import Mathlib.Data.List.OfFn
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Exact complex evaluation of the K30 raw coefficient basis

The raw exceptional certificate represents elements of `Z[zeta_36]` by
lists of twelve integers.  This module evaluates those lists at the standard
primitive thirty-sixth root of unity and proves that evaluation is injective
on lists of the intended length.  The injectivity proof uses `Phi_36`, not
floating-point arithmetic.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open Polynomial
open scoped BigOperators

noncomputable section

/-- A raw coefficient list has its intended basis length. -/
def CoeffWF (c : Coeff) : Prop := c.length = 12

/-- The standard primitive thirty-sixth root used to interpret raw data. -/
noncomputable def zeta36V71 : Complex :=
  ZMod.stdAddChar (1 : ZMod 36)

/-- The degree-less-than-twelve integer polynomial encoded by a raw list. -/
noncomputable def coeffPolynomialV71 (c : Coeff) : Polynomial Int :=
  ∑ i : Fin 12, Polynomial.monomial i.val (c.getD i.val 0)

/-- Exact evaluation of a raw coefficient list at `zeta_36`. -/
noncomputable def evalCoeff (c : Coeff) : Complex :=
  Polynomial.aeval zeta36V71 (coeffPolynomialV71 c)

theorem zeta36V71_isPrimitiveRoot :
    IsPrimitiveRoot zeta36V71 36 := by
  simpa [zeta36V71, Fuglede.frequencyOrder] using
    (Fuglede.isPrimitiveRoot_stdAddChar (1 : ZMod 36))

theorem zeta36V71_pow_stdAddChar (n : Nat) :
    zeta36V71 ^ n = ZMod.stdAddChar (n : ZMod 36) := by
  unfold zeta36V71
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp

theorem coeffPolynomialV71_coeff_lt
    (c : Coeff) (n : Nat) (hn : n < 12) :
    (coeffPolynomialV71 c).coeff n = c.getD n 0 := by
  classical
  unfold coeffPolynomialV71
  simp only [finsetSum_coeff]
  let i : Fin 12 := ⟨n, hn⟩
  rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
  · rintro j - hji
    rw [coeff_monomial, if_neg]
    rwa [← Fin.ext_iff]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem coeffPolynomialV71_coeff_ge
    (c : Coeff) (n : Nat) (hn : 12 ≤ n) :
    (coeffPolynomialV71 c).coeff n = 0 := by
  classical
  unfold coeffPolynomialV71
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [coeff_monomial, if_neg]
  omega

theorem coeffPolynomialV71_degree_lt (c : Coeff) :
    (coeffPolynomialV71 c).degree < 12 := by
  unfold coeffPolynomialV71
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
  exact Polynomial.degree_sum_fin_lt
    (fun i : Fin 12 => c.getD i.val 0)

private theorem coeffPolynomialV71_zero :
    coeffPolynomialV71 coeffZero = 0 := by
  ext n
  by_cases hn : n < 12
  · rw [coeffPolynomialV71_coeff_lt coeffZero n hn]
    simp [coeffZero]
  · rw [coeffPolynomialV71_coeff_ge coeffZero n (Nat.le_of_not_gt hn)]
    simp

private theorem coeffPolynomialV71_scalar (a : Int) :
    coeffPolynomialV71 (scalarCoeff a) = Polynomial.C a := by
  ext n
  by_cases hn : n < 12
  · rw [coeffPolynomialV71_coeff_lt (scalarCoeff a) n hn]
    interval_cases n <;> simp [scalarCoeff, Polynomial.coeff_C]
  · have hge : 12 ≤ n := Nat.le_of_not_gt hn
    have hn0 : n ≠ 0 := by omega
    rw [coeffPolynomialV71_coeff_ge (scalarCoeff a) n hge]
    simp [Polynomial.coeff_C, hn0]

private theorem coeffAdd_getD_of_lt_v71
    {left right : Coeff}
    (hleft : left.length = 12) (hright : right.length = 12)
    (n : Nat) (hn : n < 12) :
    (coeffAdd left right).getD n 0 =
      left.getD n 0 + right.getD n 0 := by
  unfold coeffAdd
  have hnleft : n < left.length := by omega
  have hnright : n < right.length := by omega
  have hnzip : n < (left.zip right).length := by
    simp [hleft, hright, hn]
  have hnmap :
      n < ((left.zip right).map
        (fun entry => entry.1 + entry.2)).length := by
    simpa using hnzip
  rw [List.getD_eq_getElem
        (l := (left.zip right).map
          (fun entry => entry.1 + entry.2))
        (d := (0 : Int)) hnmap,
      List.getD_eq_getElem (l := left) (d := (0 : Int)) hnleft,
      List.getD_eq_getElem (l := right) (d := (0 : Int)) hnright]
  simp

private theorem coeffPolynomialV71_add
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    coeffPolynomialV71 (coeffAdd left right) =
      coeffPolynomialV71 left + coeffPolynomialV71 right := by
  ext n
  by_cases hn : n < 12
  · rw [coeffPolynomialV71_coeff_lt (coeffAdd left right) n hn,
      coeffPolynomialV71_coeff_lt left n hn,
      coeffPolynomialV71_coeff_lt right n hn,
      Polynomial.coeff_add]
    exact coeffAdd_getD_of_lt_v71 hleft hright n hn
  · have hge : 12 ≤ n := Nat.le_of_not_gt hn
    rw [coeffPolynomialV71_coeff_ge (coeffAdd left right) n hge,
      coeffPolynomialV71_coeff_ge left n hge,
      coeffPolynomialV71_coeff_ge right n hge,
      Polynomial.coeff_add]
    simp

@[simp]
theorem coeffZero_wf : CoeffWF coeffZero := by
  simp [CoeffWF, coeffZero]

@[simp]
theorem scalarCoeff_wf (a : Int) : CoeffWF (scalarCoeff a) := by
  simp [CoeffWF, scalarCoeff]

theorem zetaPower_wf (exponent : Nat) :
    CoeffWF (zetaPower exponent) := by
  unfold CoeffWF zetaPower
  have hlt : exponent % 36 < 36 :=
    Nat.mod_lt exponent (by norm_num)
  interval_cases hq : exponent % 36 <;>
    simp [zetaPowerTable, hq]

theorem coeffAdd_wf
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    CoeffWF (coeffAdd left right) := by
  simp [CoeffWF, coeffAdd, hleft, hright]

private theorem foldl_coeffAdd_wf_v71
    (values : List Coeff) (acc : Coeff)
    (hacc : CoeffWF acc)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    CoeffWF (values.foldl coeffAdd acc) := by
  induction values generalizing acc with
  | nil => simpa
  | cons head tail ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact coeffAdd_wf hacc (hvalues head (by simp))
      · intro c hc
        exact hvalues c (by simp [hc])

theorem coeffSum_wf
    (values : List Coeff)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    CoeffWF (coeffSum values) := by
  unfold coeffSum
  exact foldl_coeffAdd_wf_v71 values coeffZero coeffZero_wf hvalues

theorem energy_wf (V : RawSet) (difference : Nat) :
    CoeffWF (energy V difference) := by
  unfold energy
  apply coeffSum_wf
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨v, _hv, hc⟩
  rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
  exact zetaPower_wf _

theorem gramTraceSquare_wf (U V : RawSet) :
    CoeffWF (gramTraceSquare U V) := by
  unfold gramTraceSquare
  apply coeffSum_wf
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨u, _hu, hc⟩
  rcases List.mem_map.mp hc with ⟨w, _hw, rfl⟩
  exact energy_wf V _

theorem gram_entry_wf
    {U V : RawSet} {c : Coeff} (hc : c ∈ gram U V) :
    CoeffWF c := by
  unfold gram at hc
  rcases List.mem_flatMap.mp hc with ⟨row, _hrow, hc⟩
  rcases List.mem_map.mp hc with ⟨column, _hcolumn, rfl⟩
  apply coeffSum_wf
  intro d hd
  rcases List.mem_map.mp hd with ⟨u, _hu, rfl⟩
  exact zetaPower_wf _

@[simp]
theorem evalCoeff_coeffZero : evalCoeff coeffZero = 0 := by
  unfold evalCoeff
  rw [coeffPolynomialV71_zero]
  simp

@[simp]
theorem evalCoeff_scalarCoeff (a : Int) :
    evalCoeff (scalarCoeff a) = (a : Complex) := by
  unfold evalCoeff
  rw [coeffPolynomialV71_scalar]
  simp

theorem evalCoeff_coeffAdd
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    evalCoeff (coeffAdd left right) =
      evalCoeff left + evalCoeff right := by
  unfold evalCoeff
  rw [coeffPolynomialV71_add hleft hright]
  simp

private theorem evalCoeff_foldl_coeffAdd_v71
    (values : List Coeff) (acc : Coeff)
    (hacc : CoeffWF acc)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    evalCoeff (values.foldl coeffAdd acc) =
      evalCoeff acc + (values.map evalCoeff).sum := by
  induction values generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (coeffAdd_wf hacc (hvalues head (by simp)))]
      · rw [evalCoeff_coeffAdd hacc (hvalues head (by simp))]
        ac_rfl
      · intro c hc
        exact hvalues c (by simp [hc])

theorem evalCoeff_coeffSum
    (values : List Coeff)
    (hvalues : ∀ c ∈ values, CoeffWF c) :
    evalCoeff (coeffSum values) = (values.map evalCoeff).sum := by
  unfold coeffSum
  simpa using
    (evalCoeff_foldl_coeffAdd_v71
      values coeffZero coeffZero_wf hvalues)

theorem evalCoeff_injective_of_length_twelve
    {left right : Coeff}
    (hleft : left.length = 12) (hright : right.length = 12)
    (heval : evalCoeff left = evalCoeff right) :
    left = right := by
  let P := coeffPolynomialV71 left - coeffPolynomialV71 right
  have hroot : Polynomial.aeval zeta36V71 P = 0 := by
    dsimp only [P]
    simpa [evalCoeff] using sub_eq_zero.mpr heval
  have hdvd : Polynomial.cyclotomic 36 Int ∣ P :=
    (Fuglede.cyclotomic_dvd_iff_aeval_primitive
      (by norm_num) zeta36V71_isPrimitiveRoot P).2 hroot
  have hPzero : P = 0 := by
    by_contra hPne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hPne
    have hdegree : P.degree < (12 : WithBot Nat) := by
      dsimp only [P]
      exact (Polynomial.degree_sub_le _ _).trans_lt
        (max_lt
          (coeffPolynomialV71_degree_lt left)
          (coeffPolynomialV71_degree_lt right))
    have hnatDegree : P.natDegree < 12 := by
      rw [Polynomial.degree_eq_natDegree hPne] at hdegree
      exact_mod_cast hdegree
    have htotient : Nat.totient 36 = 12 := by decide
    have hcyclotomic :
        (Polynomial.cyclotomic 36 Int).natDegree = 12 := by
      simpa [htotient] using
        (Polynomial.natDegree_cyclotomic 36 Int)
    rw [hcyclotomic] at hle
    omega
  have hpolynomial :
      coeffPolynomialV71 left = coeffPolynomialV71 right := by
    exact sub_eq_zero.mp hPzero
  apply List.ext_get_iff.mpr
  refine ⟨hleft.trans hright.symm, ?_⟩
  intro n hnleft hnright
  have hn : n < 12 := by omega
  have hcoeff := congrArg (fun Q : Polynomial Int => Q.coeff n) hpolynomial
  rw [coeffPolynomialV71_coeff_lt left n hn,
    coeffPolynomialV71_coeff_lt right n hn] at hcoeff
  calc
    left.get ⟨n, hnleft⟩ = left.getD n 0 :=
      (List.getD_eq_get
        (l := left) (d := (0 : Int)) ⟨n, hnleft⟩).symm
    _ = right.getD n 0 := hcoeff
    _ = right.get ⟨n, hnright⟩ :=
      List.getD_eq_get
        (l := right) (d := (0 : Int)) ⟨n, hnright⟩

private theorem zeta36V71_pow_six_relation :
    zeta36V71 ^ 12 = zeta36V71 ^ 6 - 1 := by
  have hprimitiveSix : IsPrimitiveRoot (zeta36V71 ^ 6) 6 := by
    convert IsPrimitiveRoot.pow_of_dvd
      zeta36V71_isPrimitiveRoot (by norm_num : 6 ≠ 0)
        (by norm_num : 6 ∣ 36) using 1 <;> norm_num
  have hroot := hprimitiveSix.isRoot_cyclotomic (by norm_num : 0 < 6)
  have hrelation :
      (zeta36V71 ^ 6) ^ 2 - zeta36V71 ^ 6 + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.cyclotomic_six] using hroot
  calc
    zeta36V71 ^ 12 = (zeta36V71 ^ 6) ^ 2 := by ring
    _ = zeta36V71 ^ 6 - 1 := by linear_combination hrelation

private theorem zeta36V71_pow_eighteen :
    zeta36V71 ^ 18 = -1 := by
  have hprimitiveTwo : IsPrimitiveRoot (zeta36V71 ^ 18) 2 := by
    convert IsPrimitiveRoot.pow_of_dvd
      zeta36V71_isPrimitiveRoot (by norm_num : 18 ≠ 0)
        (by norm_num : 18 ∣ 36) using 1 <;> norm_num
  exact hprimitiveTwo.eq_neg_one_of_two_right

private theorem zeta36V71_shift_twelve (i : Nat) :
    zeta36V71 ^ (i + 12) =
      -zeta36V71 ^ i + zeta36V71 ^ (i + 6) := by
  simp only [pow_add, zeta36V71_pow_six_relation]
  ring

private theorem zeta36V71_shift_eighteen (i : Nat) :
    zeta36V71 ^ (i + 18) = -zeta36V71 ^ i := by
  simp [pow_add, zeta36V71_pow_eighteen]

private theorem zeta36V71_pow_thirty :
    zeta36V71 ^ 30 = 1 - zeta36V71 ^ 6 := by
  calc
    zeta36V71 ^ 30 = zeta36V71 ^ 12 * zeta36V71 ^ 18 := by ring
    _ = 1 - zeta36V71 ^ 6 := by
      rw [zeta36V71_pow_six_relation, zeta36V71_pow_eighteen]
      ring

private theorem zeta36V71_shift_thirty (i : Nat) :
    zeta36V71 ^ (i + 30) =
      zeta36V71 ^ i - zeta36V71 ^ (i + 6) := by
  simp only [pow_add, zeta36V71_pow_thirty]
  ring

private theorem evalCoeff_zetaPower_lt_twelve_v71
    (q : Nat) (hq : q < 12) :
    evalCoeff (zetaPower q) = zeta36V71 ^ q := by
  interval_cases q <;>
    norm_num [evalCoeff, coeffPolynomialV71, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeff_zetaPower_twelve_eighteen_v71
    (q : Nat) (hq12 : 12 ≤ q) (hq18 : q < 18) :
    evalCoeff (zetaPower q) =
      -zeta36V71 ^ (q - 12) + zeta36V71 ^ (q - 6) := by
  interval_cases q <;>
    norm_num [evalCoeff, coeffPolynomialV71, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeff_zetaPower_eighteen_thirty_v71
    (q : Nat) (hq18 : 18 ≤ q) (hq30 : q < 30) :
    evalCoeff (zetaPower q) = -zeta36V71 ^ (q - 18) := by
  interval_cases q <;>
    norm_num [evalCoeff, coeffPolynomialV71, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

private theorem evalCoeff_zetaPower_thirty_thirtySix_v71
    (q : Nat) (hq30 : 30 ≤ q) (hq36 : q < 36) :
    evalCoeff (zetaPower q) =
      zeta36V71 ^ (q - 30) - zeta36V71 ^ (q - 24) := by
  interval_cases q <;>
    norm_num [evalCoeff, coeffPolynomialV71, zetaPower,
      zetaPowerTable, Fin.sum_univ_succ]

theorem evalCoeff_zetaPower (exponent : Nat) :
    evalCoeff (zetaPower exponent) =
      ZMod.stdAddChar (exponent : ZMod 36) := by
  rw [← zeta36V71_pow_stdAddChar exponent]
  have hpowMod :
      zeta36V71 ^ (exponent % 36) = zeta36V71 ^ exponent := by
    exact zeta36V71_isPrimitiveRoot.eq_orderOf.symm ▸
      pow_mod_orderOf zeta36V71 exponent
  rw [← hpowMod]
  let q := exponent % 36
  have hq36 : q < 36 := Nat.mod_lt exponent (by norm_num)
  have hzetaPower : zetaPower exponent = zetaPower q := by
    unfold zetaPower
    simp [q, Nat.mod_eq_of_lt hq36]
  rw [hzetaPower]
  by_cases hq12 : q < 12
  · exact evalCoeff_zetaPower_lt_twelve_v71 q hq12
  have hq12le : 12 ≤ q := Nat.le_of_not_gt hq12
  by_cases hq18 : q < 18
  · rw [evalCoeff_zetaPower_twelve_eighteen_v71 q hq12le hq18]
    symm
    convert zeta36V71_shift_twelve (q - 12) using 1 <;> congr 1 <;> omega
  have hq18le : 18 ≤ q := Nat.le_of_not_gt hq18
  by_cases hq30 : q < 30
  · rw [evalCoeff_zetaPower_eighteen_thirty_v71 q hq18le hq30]
    symm
    convert zeta36V71_shift_eighteen (q - 18) using 1 <;> congr 1 <;> omega
  have hq30le : 30 ≤ q := Nat.le_of_not_gt hq30
  rw [evalCoeff_zetaPower_thirty_thirtySix_v71 q hq30le hq36]
  symm
  convert zeta36V71_shift_thirty (q - 30) using 1 <;> congr 1 <;> omega

#print axioms zeta36V71_isPrimitiveRoot
#print axioms evalCoeff_injective_of_length_twelve
#print axioms evalCoeff_zetaPower
#print axioms gramTraceSquare_wf

end
end Fuglede.Z180K30ExceptionalRawV2
