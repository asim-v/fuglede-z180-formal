import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# Prime-power CRT coordinates for `ZMod 180`

The non-square-free modulus `180 = 4 · 9 · 5` is decomposed into its
three pairwise-coprime prime-power coordinates.  This is the natural
coordinate system for factorising exact-order Ramanujan kernels.
-/

namespace Fuglede

open scoped Function

/-- The ordered prime-power factors of `180`. -/
def crt180Modulus : Fin 3 → ℕ := ![4, 9, 5]

@[simp] theorem crt180Modulus_zero : crt180Modulus 0 = 4 := rfl
@[simp] theorem crt180Modulus_one : crt180Modulus 1 = 9 := rfl
@[simp] theorem crt180Modulus_two : crt180Modulus 2 = 5 := rfl

/-- The three prime-power CRT coordinate groups. -/
abbrev CRT180 := (i : Fin 3) → ZMod (crt180Modulus i)

theorem crt180Modulus_pairwise :
    Pairwise (Nat.Coprime on crt180Modulus) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [crt180Modulus] at hij
  all_goals norm_num [Function.onFun, crt180Modulus]

theorem crt180Modulus_prod :
    (∏ i, crt180Modulus i) = 180 := by
  decide

theorem crt180Modulus_dvd (i : Fin 3) : crt180Modulus i ∣ 180 := by
  fin_cases i <;> norm_num [crt180Modulus]

instance crt180Modulus_neZero (i : Fin 3) : NeZero (crt180Modulus i) := by
  constructor
  fin_cases i <;> norm_num [crt180Modulus]

/-- Ring Chinese-remainder equivalence in coordinate order `4,9,5`. -/
noncomputable def crt180RingEquiv : ZMod 180 ≃+* CRT180 :=
  (ZMod.ringEquivCongr crt180Modulus_prod.symm).trans
    (ZMod.prodEquivPi crt180Modulus crt180Modulus_pairwise)

/-- Additive equivalence underlying `crt180RingEquiv`. -/
noncomputable def crt180AddEquiv : ZMod 180 ≃+ CRT180 :=
  crt180RingEquiv.toAddEquiv

noncomputable def toCRT180 (x : ZMod 180) : CRT180 :=
  crt180AddEquiv x

noncomputable def fromCRT180 (x : CRT180) : ZMod 180 :=
  crt180AddEquiv.symm x

@[simp]
theorem fromCRT180_toCRT180 (x : ZMod 180) :
    fromCRT180 (toCRT180 x) = x :=
  crt180AddEquiv.symm_apply_apply x

@[simp]
theorem toCRT180_fromCRT180 (x : CRT180) :
    toCRT180 (fromCRT180 x) = x :=
  crt180AddEquiv.apply_symm_apply x

@[simp]
theorem toCRT180_zero : toCRT180 0 = 0 :=
  crt180AddEquiv.map_zero

@[simp]
theorem toCRT180_add (x y : ZMod 180) :
    toCRT180 (x + y) = toCRT180 x + toCRT180 y :=
  crt180AddEquiv.map_add x y

@[simp]
theorem toCRT180_neg (x : ZMod 180) :
    toCRT180 (-x) = -toCRT180 x :=
  crt180AddEquiv.map_neg x

@[simp]
theorem toCRT180_sub (x y : ZMod 180) :
    toCRT180 (x - y) = toCRT180 x - toCRT180 y :=
  crt180AddEquiv.map_sub x y

@[simp]
theorem toCRT180_mul (x y : ZMod 180) :
    toCRT180 (x * y) = toCRT180 x * toCRT180 y :=
  crt180RingEquiv.map_mul x y

/-- Each coordinate is ordinary reduction modulo `4`, `9`, or `5`. -/
@[simp]
theorem toCRT180_apply (x : ZMod 180) (i : Fin 3) :
    toCRT180 x i = (ZMod.cast x : ZMod (crt180Modulus i)) := by
  change
    ((Pi.evalRingHom (fun i ↦ ZMod (crt180Modulus i)) i).comp
      crt180RingEquiv.toRingHom) x = ZMod.cast x
  have hhom :
      (Pi.evalRingHom (fun i ↦ ZMod (crt180Modulus i)) i).comp
          crt180RingEquiv.toRingHom =
        ZMod.castHom (crt180Modulus_dvd i) (ZMod (crt180Modulus i)) :=
    Subsingleton.elim _ _
  rw [hhom, ZMod.castHom_apply]

theorem toCRT180_injective : Function.Injective toCRT180 :=
  crt180AddEquiv.injective

theorem toCRT180_surjective : Function.Surjective toCRT180 :=
  crt180AddEquiv.surjective

theorem card_CRT180 : Fintype.card CRT180 = 180 := by
  calc
    Fintype.card CRT180 = Fintype.card (ZMod 180) :=
      Fintype.card_congr crt180AddEquiv.toEquiv.symm
    _ = 180 := by simp

end Fuglede
