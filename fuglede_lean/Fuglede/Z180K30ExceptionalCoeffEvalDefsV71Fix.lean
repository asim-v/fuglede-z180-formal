import Fuglede.Z180K30ExceptionalRawCoreV2
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-!
# Definitions for exact evaluation of the K30 raw coefficient basis

This is the minimal repaired base of the coefficient-evaluation bridge.
It contains only the exact evaluator, the primitive-root fact, and elementary
length invariants.  Polynomial injectivity and the finite `zetaPower` table
are deliberately left to later modules.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open Polynomial
open scoped BigOperators

noncomputable section

/-- A coefficient list has the intended twelve coordinates. -/
def CoeffWF (c : Coeff) : Prop := c.length = 12

/-- The standard primitive thirty-sixth root used by the raw evaluator. -/
noncomputable def zeta36V71Fix : Complex :=
  ZMod.stdAddChar (1 : ZMod 36)

/-- The integer polynomial represented by the first twelve raw coordinates. -/
noncomputable def coeffPolynomialV71Fix (c : Coeff) : Polynomial Int :=
  ∑ i : Fin 12, Polynomial.monomial i.val (c.getD i.val 0)

/-- Exact evaluation of a raw coefficient list at the standard root. -/
noncomputable def evalCoeffV71Fix (c : Coeff) : Complex :=
  Polynomial.aeval zeta36V71Fix (coeffPolynomialV71Fix c)

theorem zeta36V71Fix_isPrimitiveRoot :
    IsPrimitiveRoot zeta36V71Fix 36 := by
  have horder :
      Fuglede.frequencyOrder 36 (1 : ZMod 36) = 36 := by
    decide
  simpa [zeta36V71Fix, horder] using
    (Fuglede.isPrimitiveRoot_stdAddChar (1 : ZMod 36))

theorem coeffZero_length_v71Fix : coeffZero.length = 12 := by
  simp [coeffZero]

theorem scalarCoeff_length_v71Fix (a : Int) :
    (scalarCoeff a).length = 12 := by
  simp [scalarCoeff]

theorem coeffAdd_length_v71Fix
    {left right : Coeff}
    (hleft : left.length = 12) (hright : right.length = 12) :
    (coeffAdd left right).length = 12 := by
  unfold coeffAdd
  simp only [List.length_map, List.length_zip, hleft, hright]
  norm_num

@[simp]
theorem coeffZero_wf_v71Fix : CoeffWF coeffZero := by
  unfold CoeffWF
  exact coeffZero_length_v71Fix

@[simp]
theorem scalarCoeff_wf_v71Fix (a : Int) :
    CoeffWF (scalarCoeff a) := by
  unfold CoeffWF
  exact scalarCoeff_length_v71Fix a

theorem coeffAdd_wf_v71Fix
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    CoeffWF (coeffAdd left right) := by
  unfold CoeffWF at hleft hright ⊢
  exact coeffAdd_length_v71Fix hleft hright

#print axioms zeta36V71Fix_isPrimitiveRoot
#print axioms coeffAdd_wf_v71Fix

end
end Fuglede.Z180K30ExceptionalRawV2
