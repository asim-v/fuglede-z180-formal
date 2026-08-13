import Fuglede.Z180FiveLevelCardinality
import Fuglede.Z180SmallCardinality
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Exact phase geometry for the cardinality-six defect

The five-level descent reduces the only double fibre to an equality
`u + v = w` among unit complex phases.  This module proves algebraically that
the two ratios `u / w` and `v / w` are primitive sixth roots.  It then records
the corresponding exact statements for the standard characters of
`ZMod 180` at frequency `30`, without trigonometry or numerical evaluation.
-/

namespace Fuglede

open Polynomial
open scoped ComplexConjugate

/-- If two unit complex numbers add to a third, each summand divided by the
sum is a primitive sixth root of unity. -/
theorem unit_pair_sum_unit_ratios_primitive_six
    {u v w : ℂ}
    (hu : u * star u = 1) (hv : v * star v = 1)
    (hw : w * star w = 1) (hsum : u + v = w) :
    IsPrimitiveRoot (u * star w) 6 ∧
      IsPrimitiveRoot (v * star w) 6 := by
  let proveLeft : ∀ {a b : ℂ},
      a * star a = 1 → b * star b = 1 → a + b = w →
        IsPrimitiveRoot (a * star w) 6 := by
    intro a b ha hb hab
    let x : ℂ := a * star w
    let y : ℂ := b * star w
    have hxunitRaw :
        (a * star w) * star (a * star w) = 1 := by
      rw [star_mul, star_star]
      calc
        (a * star w) * (w * star a) =
            (a * star a) * (w * star w) := by ring
        _ = 1 := by rw [ha, hw, one_mul]
    have hxunit : x * star x = 1 := by
      simpa only [x] using hxunitRaw
    have hyunitRaw :
        (b * star w) * star (b * star w) = 1 := by
      rw [star_mul, star_star]
      calc
        (b * star w) * (w * star b) =
            (b * star b) * (w * star w) := by ring
        _ = 1 := by rw [hb, hw, one_mul]
    have hyunit : y * star y = 1 := by
      simpa only [y] using hyunitRaw
    have hxy_sum : x + y = 1 := by
      dsimp [x, y]
      calc
        a * star w + b * star w = (a + b) * star w := by ring
        _ = w * star w := by rw [hab]
        _ = 1 := hw
    have hstar_sum : star x + star y = 1 := by
      have h := congrArg (starRingEnd ℂ) hxy_sum
      simpa using h
    have hxy_mul : x * y = 1 := by
      calc
        x * y = x * y * (star x + star y) := by rw [hstar_sum, mul_one]
        _ = y * (x * star x) + x * (y * star y) := by ring
        _ = y + x := by rw [hxunit, hyunit, mul_one, mul_one]
        _ = 1 := by simpa [add_comm] using hxy_sum
    have hxquad : x ^ 2 - x + 1 = 0 := by
      linear_combination x * hxy_sum - hxy_mul
    have hroot : IsRoot (cyclotomic 6 ℂ) x := by
      rw [cyclotomic_six]
      simpa [IsRoot, eval_add, eval_sub, eval_pow] using hxquad
    exact (isRoot_cyclotomic_iff (R := ℂ)).mp hroot
  constructor
  · exact proveLeft hu hv hsum
  · exact proveLeft hv hu (by simpa [add_comm] using hsum)

/-- The two primitive-six ratios supplied by the same equation are distinct. -/
theorem unit_pair_sum_unit_ratios_ne
    {u v w : ℂ}
    (hu : u * star u = 1) (hv : v * star v = 1)
    (hw : w * star w = 1) (hsum : u + v = w) :
    u * star w ≠ v * star w := by
  intro heq
  let x : ℂ := u * star w
  have hxunitRaw :
      (u * star w) * star (u * star w) = 1 := by
    rw [star_mul, star_star]
    calc
      (u * star w) * (w * star u) =
          (u * star u) * (w * star w) := by ring
      _ = 1 := by rw [hu, hw, one_mul]
  have hxunit : x * star x = 1 := by
    simpa only [x] using hxunitRaw
  have hnormalized : x + x = 1 := by
    dsimp [x]
    calc
      u * star w + u * star w =
          u * star w + v * star w := by rw [heq]
      _ = (u + v) * star w := by ring
      _ = w * star w := by rw [hsum]
      _ = 1 := hw
  have hxhalf : x = (1 / 2 : ℂ) := by
    linear_combination (1 / 2 : ℂ) * hnormalized
  rw [hxhalf] at hxunit
  norm_num at hxunit

/-- Multiplication by `30` in `ZMod 180` carries the same character as
reduction modulo six. -/
theorem z180_stdAddChar_mul_thirty_eq_cast_six (x : ZMod 180) :
    ZMod.stdAddChar (x * 30) =
      ZMod.stdAddChar (ZMod.cast x : ZMod 6) := by
  calc
    ZMod.stdAddChar (x * 30) =
        ZMod.stdAddChar ((x.val : ZMod 180) * 30) := by
      rw [ZMod.natCast_zmod_val]
    _ = ZMod.stdAddChar ((((x.val : ℤ) * 30 : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ =
        Complex.exp
          (2 * Real.pi * Complex.I * (((x.val : ℤ) * 30 : ℤ) : ℂ) /
            (180 : ℂ)) := ZMod.stdAddChar_coe _
    _ = Complex.exp
          (2 * Real.pi * Complex.I * ((x.val : ℤ) : ℂ) / (6 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar (((x.val : ℤ) : ZMod 6)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar (ZMod.cast x : ZMod 6) := by
      rw [Int.cast_natCast, ZMod.cast_eq_val]

/-- Equal order-six phases are exactly equality of residues modulo six. -/
theorem z180_cast_six_eq_of_order_six_phase_eq
    {a b : ZMod 180}
    (h : ZMod.stdAddChar (a * 30) = ZMod.stdAddChar (b * 30)) :
    (ZMod.cast a : ZMod 6) = ZMod.cast b := by
  rw [z180_stdAddChar_mul_thirty_eq_cast_six,
    z180_stdAddChar_mul_thirty_eq_cast_six] at h
  exact ZMod.injective_stdAddChar h

/-- The double-fibre equation forces both differences from a singleton phase
to have additive order six after reduction modulo six. -/
theorem z180_cast_six_frequencyOrder_of_pair_phase_sum
    {a b r : ZMod 180}
    (hsum : ZMod.stdAddChar (a * 30) + ZMod.stdAddChar (b * 30) =
      ZMod.stdAddChar (r * 30)) :
    frequencyOrder 6 ((ZMod.cast a : ZMod 6) - ZMod.cast r) = 6 ∧
      frequencyOrder 6 ((ZMod.cast b : ZMod 6) - ZMod.cast r) = 6 := by
  rw [z180_stdAddChar_mul_thirty_eq_cast_six,
    z180_stdAddChar_mul_thirty_eq_cast_six,
    z180_stdAddChar_mul_thirty_eq_cast_six] at hsum
  let ua : ℂ := ZMod.stdAddChar (ZMod.cast a : ZMod 6)
  let ub : ℂ := ZMod.stdAddChar (ZMod.cast b : ZMod 6)
  let ur : ℂ := ZMod.stdAddChar (ZMod.cast r : ZMod 6)
  have huaRaw : ZMod.stdAddChar (ZMod.cast a : ZMod 6) *
      star (ZMod.stdAddChar (ZMod.cast a : ZMod 6)) = 1 := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    simp
  have hua : ua * star ua = 1 := by simpa only [ua] using huaRaw
  have hubRaw : ZMod.stdAddChar (ZMod.cast b : ZMod 6) *
      star (ZMod.stdAddChar (ZMod.cast b : ZMod 6)) = 1 := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    simp
  have hub : ub * star ub = 1 := by simpa only [ub] using hubRaw
  have hurRaw : ZMod.stdAddChar (ZMod.cast r : ZMod 6) *
      star (ZMod.stdAddChar (ZMod.cast r : ZMod 6)) = 1 := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    simp
  have hur : ur * star ur = 1 := by simpa only [ur] using hurRaw
  have hgeom := unit_pair_sum_unit_ratios_primitive_six
    hua hub hur hsum
  have haRatioRaw :
      ZMod.stdAddChar (ZMod.cast a : ZMod 6) *
        star (ZMod.stdAddChar (ZMod.cast r : ZMod 6)) =
      ZMod.stdAddChar ((ZMod.cast a : ZMod 6) - ZMod.cast r) := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have haRatio : ua * star ur =
      ZMod.stdAddChar ((ZMod.cast a : ZMod 6) - ZMod.cast r) := by
    simpa only [ua, ur] using haRatioRaw
  have hbRatioRaw :
      ZMod.stdAddChar (ZMod.cast b : ZMod 6) *
        star (ZMod.stdAddChar (ZMod.cast r : ZMod 6)) =
      ZMod.stdAddChar ((ZMod.cast b : ZMod 6) - ZMod.cast r) := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hbRatio : ub * star ur =
      ZMod.stdAddChar ((ZMod.cast b : ZMod 6) - ZMod.cast r) := by
    simpa only [ub, ur] using hbRatioRaw
  constructor
  · have hprim : IsPrimitiveRoot
        (ZMod.stdAddChar ((ZMod.cast a : ZMod 6) - ZMod.cast r)) 6 := by
      rw [← haRatio]
      exact hgeom.1
    have hcanonical :=
      isPrimitiveRoot_stdAddChar ((ZMod.cast a : ZMod 6) - ZMod.cast r)
    exact hcanonical.eq_orderOf.trans hprim.eq_orderOf.symm
  · have hprim : IsPrimitiveRoot
        (ZMod.stdAddChar ((ZMod.cast b : ZMod 6) - ZMod.cast r)) 6 := by
      rw [← hbRatio]
      exact hgeom.2
    have hcanonical :=
      isPrimitiveRoot_stdAddChar ((ZMod.cast b : ZMod 6) - ZMod.cast r)
    exact hcanonical.eq_orderOf.trans hprim.eq_orderOf.symm

/-- The only elements of additive order six in `ZMod 6` are `1` and `-1`. -/
theorem zmod6_eq_one_or_neg_one_of_frequencyOrder_eq_six
    (z : ZMod 6) (hz : frequencyOrder 6 z = 6) :
    z = 1 ∨ z = -1 := by
  exact (by decide : ∀ t : ZMod 6,
    frequencyOrder 6 t = 6 → t = 1 ∨ t = -1) z hz

/-- Fully discrete form of the double-fibre phase equation: the two residues
are the opposite primitive classes around the singleton residue. -/
theorem z180_cast_six_pair_normal_form_of_phase_sum
    {a b r : ZMod 180}
    (hsum : ZMod.stdAddChar (a * 30) + ZMod.stdAddChar (b * 30) =
      ZMod.stdAddChar (r * 30)) :
    (((ZMod.cast a : ZMod 6) - ZMod.cast r = 1 ∧
        (ZMod.cast b : ZMod 6) - ZMod.cast r = -1) ∨
      ((ZMod.cast a : ZMod 6) - ZMod.cast r = -1 ∧
        (ZMod.cast b : ZMod 6) - ZMod.cast r = 1)) := by
  obtain ⟨ha, hb⟩ := z180_cast_six_frequencyOrder_of_pair_phase_sum hsum
  have ha' := zmod6_eq_one_or_neg_one_of_frequencyOrder_eq_six _ ha
  have hb' := zmod6_eq_one_or_neg_one_of_frequencyOrder_eq_six _ hb
  have hratioNe := unit_pair_sum_unit_ratios_ne
    (z180_char_unit (a * 30)) (z180_char_unit (b * 30))
    (z180_char_unit (r * 30)) hsum
  have hresNe :
      (ZMod.cast a : ZMod 6) - ZMod.cast r ≠
        (ZMod.cast b : ZMod 6) - ZMod.cast r := by
    intro heq
    apply hratioNe
    rw [z180_char_ratio a r 30, z180_char_ratio b r 30]
    rw [z180_stdAddChar_mul_thirty_eq_cast_six,
      z180_stdAddChar_mul_thirty_eq_cast_six]
    apply congrArg ZMod.stdAddChar
    simpa using heq
  rcases ha' with ha' | ha'
  · rcases hb' with hb' | hb'
    · exact (hresNe (ha'.trans hb'.symm)).elim
    · exact Or.inl ⟨ha', hb'⟩
  · rcases hb' with hb' | hb'
    · exact Or.inr ⟨ha', hb'⟩
    · exact (hresNe (ha'.trans hb'.symm)).elim

end Fuglede
