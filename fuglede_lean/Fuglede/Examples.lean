import Fuglede

namespace Fuglede.Examples

open Fuglede
open Polynomial

/-- In `Z/6Z`, `{0,1}` tiles with the even residues.  This is a kernel-checked
smoke test for the executable tiling definition. -/
example : Tiles ({0, 1} : Finset (ZMod 6)) ({0, 2, 4} : Finset (ZMod 6)) := by
  decide

/-- The generic cardinality theorem recovers `2 * 3 = 6` from that certificate. -/
example :
    ({0, 1} : Finset (ZMod 6)).card * ({0, 2, 4} : Finset (ZMod 6)).card = 6 := by
  apply card_mul_eq_card_of_tiles
  decide

/-- The same two-point set has the exact spectrum `{0,3}`.  The proof checks
the quotient by `Φ₂ = X + 1`; no approximate complex arithmetic is used. -/
example : CyclotomicSpectrum 6
    ({0, 1} : Finset (ZMod 6)) ({0, 3} : Finset (ZMod 6)) := by
  norm_num [CyclotomicSpectrum]
  constructor
  · decide
  · constructor
    · intro _
      unfold CyclotomicZero
      rw [show frequencyOrder 6 (-3 : ZMod 6) = 2 by decide]
      refine ⟨1, ?_⟩
      simp only [cyclotomic_two, mul_one]
      have h01 : (0 : ZMod 6) ≠ 1 := by decide
      have hval : (1 : ZMod 6).val = 1 := by decide
      simp [maskPolynomial, h01, hval, add_comm]
    · intro _
      unfold CyclotomicZero
      rw [show frequencyOrder 6 (3 : ZMod 6) = 2 by decide]
      refine ⟨1, ?_⟩
      simp only [cyclotomic_two, mul_one]
      have h01 : (0 : ZMod 6) ≠ 1 := by decide
      have hval : (1 : ZMod 6).val = 1 := by decide
      simp [maskPolynomial, h01, hval, add_comm]

end Fuglede.Examples
