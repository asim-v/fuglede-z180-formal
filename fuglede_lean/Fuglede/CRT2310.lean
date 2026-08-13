import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# Chinese-remainder coordinates for `ZMod 2310`

This module fixes the five square-free prime coordinates of `2310` and
packages the Chinese remainder theorem as an explicit additive equivalence.
The named forward and inverse maps, their round trips, and the cardinality
lemmas are intended as the base layer for transporting difference supports.
-/

namespace Fuglede

open scoped Function

/-- The ordered prime moduli whose product is `2310`. -/
def crt2310Modulus : Fin 5 → ℕ := ![2, 3, 5, 7, 11]

@[simp] theorem crt2310Modulus_zero : crt2310Modulus 0 = 2 := rfl
@[simp] theorem crt2310Modulus_one : crt2310Modulus 1 = 3 := rfl
@[simp] theorem crt2310Modulus_two : crt2310Modulus 2 = 5 := rfl
@[simp] theorem crt2310Modulus_three : crt2310Modulus 3 = 7 := rfl
@[simp] theorem crt2310Modulus_four : crt2310Modulus 4 = 11 := rfl

/-- The dependent product of the five CRT coordinate groups. -/
abbrev CRT2310 := (i : Fin 5) → ZMod (crt2310Modulus i)

theorem crt2310Modulus_pairwise :
    Pairwise (Nat.Coprime on crt2310Modulus) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [crt2310Modulus] at hij
  all_goals norm_num [Function.onFun, crt2310Modulus]

theorem crt2310Modulus_prod :
    (∏ i, crt2310Modulus i) = 2310 := by
  decide

theorem crt2310Modulus_dvd (i : Fin 5) : crt2310Modulus i ∣ 2310 := by
  fin_cases i <;> norm_num [crt2310Modulus]

instance crt2310Modulus_neZero (i : Fin 5) : NeZero (crt2310Modulus i) := by
  constructor
  fin_cases i <;> norm_num [crt2310Modulus]

/-- Ring-level Chinese-remainder equivalence in the fixed coordinate order
`2, 3, 5, 7, 11`. -/
noncomputable def crt2310RingEquiv : ZMod 2310 ≃+* CRT2310 :=
  (ZMod.ringEquivCongr crt2310Modulus_prod.symm).trans
    (ZMod.prodEquivPi crt2310Modulus crt2310Modulus_pairwise)

/-- The additive equivalence underlying `crt2310RingEquiv`. -/
noncomputable def crt2310AddEquiv : ZMod 2310 ≃+ CRT2310 :=
  crt2310RingEquiv.toAddEquiv

/-- Send a residue modulo `2310` to its five CRT coordinates. -/
noncomputable def toCRT2310 (x : ZMod 2310) : CRT2310 :=
  crt2310AddEquiv x

/-- Reconstruct a residue modulo `2310` from its five CRT coordinates. -/
noncomputable def fromCRT2310 (x : CRT2310) : ZMod 2310 :=
  crt2310AddEquiv.symm x

@[simp]
theorem fromCRT2310_toCRT2310 (x : ZMod 2310) :
    fromCRT2310 (toCRT2310 x) = x := by
  exact crt2310AddEquiv.symm_apply_apply x

@[simp]
theorem toCRT2310_fromCRT2310 (x : CRT2310) :
    toCRT2310 (fromCRT2310 x) = x := by
  exact crt2310AddEquiv.apply_symm_apply x

@[simp]
theorem toCRT2310_zero : toCRT2310 0 = 0 := by
  exact crt2310AddEquiv.map_zero

@[simp]
theorem toCRT2310_add (x y : ZMod 2310) :
    toCRT2310 (x + y) = toCRT2310 x + toCRT2310 y := by
  exact crt2310AddEquiv.map_add x y

@[simp]
theorem toCRT2310_neg (x : ZMod 2310) :
    toCRT2310 (-x) = -toCRT2310 x := by
  exact crt2310AddEquiv.map_neg x

@[simp]
theorem toCRT2310_sub (x y : ZMod 2310) :
    toCRT2310 (x - y) = toCRT2310 x - toCRT2310 y := by
  exact crt2310AddEquiv.map_sub x y

/-- Each CRT coordinate is ordinary reduction modulo its corresponding
prime.  This makes the equivalence usable without unfolding its construction. -/
@[simp]
theorem toCRT2310_apply (x : ZMod 2310) (i : Fin 5) :
    toCRT2310 x i = (ZMod.cast x : ZMod (crt2310Modulus i)) := by
  change
    ((Pi.evalRingHom (fun i ↦ ZMod (crt2310Modulus i)) i).comp
      crt2310RingEquiv.toRingHom) x = ZMod.cast x
  have hhom :
      (Pi.evalRingHom (fun i ↦ ZMod (crt2310Modulus i)) i).comp
          crt2310RingEquiv.toRingHom =
        ZMod.castHom (crt2310Modulus_dvd i) (ZMod (crt2310Modulus i)) :=
    Subsingleton.elim _ _
  rw [hhom, ZMod.castHom_apply]

theorem toCRT2310_injective : Function.Injective toCRT2310 :=
  crt2310AddEquiv.injective

theorem toCRT2310_surjective : Function.Surjective toCRT2310 :=
  crt2310AddEquiv.surjective

theorem toCRT2310_eq_iff {x y : ZMod 2310} :
    toCRT2310 x = toCRT2310 y ↔ x = y := by
  constructor
  · exact fun h ↦ toCRT2310_injective h
  · exact fun h ↦ congrArg toCRT2310 h

theorem card_CRT2310 : Fintype.card CRT2310 = 2310 := by
  calc
    Fintype.card CRT2310 = Fintype.card (ZMod 2310) :=
      Fintype.card_congr crt2310AddEquiv.toEquiv.symm
    _ = 2310 := by simp

theorem card_zmod_2310 : Fintype.card (ZMod 2310) = 2310 := by
  simp

/-- Prime coordinates on which a residue is nonzero. -/
noncomputable def crt2310Support (x : ZMod 2310) : Finset (Fin 5) :=
  Finset.univ.filter fun i ↦ toCRT2310 x i ≠ 0

@[simp]
theorem mem_crt2310Support {x : ZMod 2310} {i : Fin 5} :
    i ∈ crt2310Support x ↔ toCRT2310 x i ≠ 0 := by
  classical
  simp [crt2310Support]

/-- A coordinate belongs to the support of a difference exactly when the two
endpoints have distinct coordinates there. -/
theorem mem_crt2310Support_sub_iff (x y : ZMod 2310) (i : Fin 5) :
    i ∈ crt2310Support (x - y) ↔ toCRT2310 x i ≠ toCRT2310 y i := by
  classical
  rw [mem_crt2310Support, congrFun (toCRT2310_sub x y) i]
  simp only [Pi.sub_apply, sub_ne_zero]

theorem card_crt2310Support_le_five (x : ZMod 2310) :
    (crt2310Support x).card ≤ 5 := by
  classical
  simpa [crt2310Support] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin 5)))
      (p := fun i ↦ toCRT2310 x i ≠ 0))

end Fuglede
