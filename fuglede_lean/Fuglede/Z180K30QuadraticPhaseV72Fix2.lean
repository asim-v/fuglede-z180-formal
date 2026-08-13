import Mathlib.Tactic

/-!
# A quadratic phase lemma for the K30 rank-two reduction

Three distinct values cannot satisfy the same genuine quadratic equation.
Consequently, if two unit-modulus rows span a third unit-modulus row with
both coefficients nonzero, the coordinatewise ratio of the first two rows
takes at most two values.  This is the algebraic core of the projective
rank-two alternative; it uses no finite census.
-/

namespace Fuglede

open scoped ComplexConjugate

theorem quadratic_third_root_is_one_of_two_v72Fix2
    {A B C x y z : Complex}
    (hA : A ≠ 0) (hxy : x ≠ y)
    (hx : A * x ^ 2 + B * x + C = 0)
    (hy : A * y ^ 2 + B * y + C = 0)
    (hz : A * z ^ 2 + B * z + C = 0) :
    z = x ∨ z = y := by
  by_cases hzx : z = x
  · exact Or.inl hzx
  · right
    have hxz : x ≠ z := by
      intro hxz
      exact hzx hxz.symm
    have hxyFactor : (x - y) * (A * (x + y) + B) = 0 := by
      calc
        (x - y) * (A * (x + y) + B) =
            (A * x ^ 2 + B * x + C) -
              (A * y ^ 2 + B * y + C) := by ring
        _ = 0 := by rw [hx, hy]; ring
    have hxzFactor : (x - z) * (A * (x + z) + B) = 0 := by
      calc
        (x - z) * (A * (x + z) + B) =
            (A * x ^ 2 + B * x + C) -
              (A * z ^ 2 + B * z + C) := by ring
        _ = 0 := by rw [hx, hz]; ring
    have hxyLinear : A * (x + y) + B = 0 :=
      (mul_eq_zero.mp hxyFactor).resolve_left (sub_ne_zero.mpr hxy)
    have hxzLinear : A * (x + z) + B = 0 :=
      (mul_eq_zero.mp hxzFactor).resolve_left (sub_ne_zero.mpr hxz)
    have hyz : A * (y - z) = 0 := by
      calc
        A * (y - z) =
            (A * (x + y) + B) - (A * (x + z) + B) := by ring
        _ = 0 := by rw [hxyLinear, hxzLinear]; ring
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hyz).resolve_left hA)).symm

theorem unit_affine_phase_has_two_values_v72Fix2
    (a b : Complex) (t z : Fin 6 → Complex)
    (hleading : star a * b ≠ 0)
    (htUnit : ∀ j, star (t j) * t j = 1)
    (hzUnit : ∀ j, star (z j) * z j = 1)
    (hzAffine : ∀ j, z j = a + b * t j) :
    ∃ p q : Fin 6, ∀ j, t j = t p ∨ t j = t q := by
  have hquadratic (j : Fin 6) :
      (star a * b) * (t j) ^ 2 +
          (star a * a + star b * b - 1) * t j + star b * a = 0 := by
    have hunitT := htUnit j
    have hunitZ := hzUnit j
    rw [hzAffine j, star_add, star_mul] at hunitZ
    calc
      (star a * b) * (t j) ^ 2 +
          (star a * a + star b * b - 1) * t j + star b * a =
        (star (a + b * t j) * (a + b * t j) - 1) * t j := by
          rw [star_add, star_mul]
          linear_combination
            -(star b * (a + b * t j)) * hunitT
      _ = 0 := by
        rw [star_add, star_mul, hunitZ]
        ring
  by_cases hall : ∀ j, t j = t 0
  · exact ⟨0, 0, fun j => Or.inl (hall j)⟩
  · have hexists : ∃ j, t j ≠ t 0 := not_forall.mp hall
    obtain ⟨q, hq⟩ := hexists
    refine ⟨0, q, ?_⟩
    intro j
    exact quadratic_third_root_is_one_of_two_v72Fix2
      hleading hq.symm (hquadratic 0) (hquadratic q) (hquadratic j)

#print axioms quadratic_third_root_is_one_of_two_v72Fix2
#print axioms unit_affine_phase_has_two_values_v72Fix2

end Fuglede
