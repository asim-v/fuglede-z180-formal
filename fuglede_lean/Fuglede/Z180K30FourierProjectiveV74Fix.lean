import Fuglede.Z180K30RankTwoProjectiveV73Fix
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-!
# Projective classes of six-by-six Fourier blocks

This module specializes the abstract rank-two projective dichotomy to a
`ZMod 36` Fourier block and records the exact congruence equation forced by
two proportional rows or columns.
-/

namespace Fuglede

open scoped ComplexConjugate

noncomputable def z36FourierBlockV74Fix
    (U V : Fin 6 → ZMod 36) : Matrix (Fin 6) (Fin 6) Complex :=
  fun a l => ZMod.stdAddChar (U a * V l)

@[simp]
theorem z36FourierBlockV74Fix_apply
    (U V : Fin 6 → ZMod 36) (a l : Fin 6) :
    z36FourierBlockV74Fix U V a l = ZMod.stdAddChar (U a * V l) := rfl

theorem z36FourierBlockV74Fix_entry_unit
    (U V : Fin 6 → ZMod 36) (a l : Fin 6) :
    star (z36FourierBlockV74Fix U V a l) *
        z36FourierBlockV74Fix U V a l = 1 := by
  rw [z36FourierBlockV74Fix_apply, star_stdAddChar,
    ← AddChar.map_add_eq_mul]
  simp

theorem z36FourierBlockV74Fix_projective_dichotomy_of_span_two
    (U V : Fin 6 → ZMod 36)
    (p q : Fin 6) (alpha beta : Fin 6 → Complex)
    (hspan : ∀ i j,
      z36FourierBlockV74Fix U V i j =
        alpha i * z36FourierBlockV74Fix U V p j +
          beta i * z36FourierBlockV74Fix U V q j) :
    Z180K30RowsCoveredByTwoProjectiveV73Fix
        (z36FourierBlockV74Fix U V) p q ∨
      ∃ c d : Fin 6,
        Z180K30ColumnsCoveredByTwoProjectiveV73Fix
          (z36FourierBlockV74Fix U V) c d := by
  exact rows_span_two_unit_projective_dichotomy_v73Fix
    (z36FourierBlockV74Fix U V) p q alpha beta
    (z36FourierBlockV74Fix_entry_unit U V) hspan

private theorem stdAddChar_ne_zero_v74Fix (x : ZMod 36) :
    ZMod.stdAddChar x ≠ 0 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

theorem z36FourierBlockV74Fix_row_proportional_zero
    (U V : Fin 6 → ZMod 36) (a p : Fin 6) (scale : Complex)
    (hrow : ∀ l,
      z36FourierBlockV74Fix U V a l =
        scale * z36FourierBlockV74Fix U V p l) :
    ∀ l, (U a - U p) * (V l - V 0) = 0 := by
  intro l
  have hcross :
      ZMod.stdAddChar (U a * V l) * ZMod.stdAddChar (U p * V 0) =
        ZMod.stdAddChar (U a * V 0) * ZMod.stdAddChar (U p * V l) := by
    simpa only [z36FourierBlockV74Fix_apply] using
      calc
        z36FourierBlockV74Fix U V a l *
              z36FourierBlockV74Fix U V p 0 =
            (scale * z36FourierBlockV74Fix U V p l) *
              z36FourierBlockV74Fix U V p 0 := by rw [hrow l]
        _ = (scale * z36FourierBlockV74Fix U V p 0) *
              z36FourierBlockV74Fix U V p l := by ring
        _ = z36FourierBlockV74Fix U V a 0 *
              z36FourierBlockV74Fix U V p l := by rw [← hrow 0]
  apply ZMod.injective_stdAddChar
  rw [AddChar.map_zero_eq_one]
  have hexpand :
      (U a - U p) * (V l - V 0) =
        U a * V l + U p * V 0 +
          (-(U a * V 0) + -(U p * V l)) := by ring
  rw [hexpand]
  simp only [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  rw [hcross]
  field_simp [stdAddChar_ne_zero_v74Fix]

theorem z36FourierBlockV74Fix_column_proportional_zero
    (U V : Fin 6 → ZMod 36) (l e : Fin 6) (scale : Complex)
    (hcolumn : ∀ a,
      z36FourierBlockV74Fix U V a l =
        scale * z36FourierBlockV74Fix U V a e) :
    ∀ a, (U a - U 0) * (V l - V e) = 0 := by
  intro a
  have hcross :
      ZMod.stdAddChar (U a * V l) * ZMod.stdAddChar (U 0 * V e) =
        ZMod.stdAddChar (U 0 * V l) * ZMod.stdAddChar (U a * V e) := by
    simpa only [z36FourierBlockV74Fix_apply] using
      calc
        z36FourierBlockV74Fix U V a l *
              z36FourierBlockV74Fix U V 0 e =
            (scale * z36FourierBlockV74Fix U V a e) *
              z36FourierBlockV74Fix U V 0 e := by rw [hcolumn a]
        _ = (scale * z36FourierBlockV74Fix U V 0 e) *
              z36FourierBlockV74Fix U V a e := by ring
        _ = z36FourierBlockV74Fix U V 0 l *
              z36FourierBlockV74Fix U V a e := by rw [← hcolumn 0]
  apply ZMod.injective_stdAddChar
  rw [AddChar.map_zero_eq_one]
  have hexpand :
      (U a - U 0) * (V l - V e) =
        U a * V l + U 0 * V e +
          (-(U 0 * V l) + -(U a * V e)) := by ring
  rw [hexpand]
  simp only [AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
  rw [hcross]
  field_simp [stdAddChar_ne_zero_v74Fix]

#print axioms z36FourierBlockV74Fix_projective_dichotomy_of_span_two
#print axioms z36FourierBlockV74Fix_row_proportional_zero
#print axioms z36FourierBlockV74Fix_column_proportional_zero

end Fuglede
