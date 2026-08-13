import Fuglede.Z180K30ExceptionalProjectiveScalarZeroV89
import Mathlib.Tactic

/-!
# Ordered-difference scalar kernel for the K30 projective audit

This module is independent of every generated V89 leaf.  It exposes the
coefficient-zero computation as a bilinear sum over the two ordered-difference
lists and proves the symmetry needed to use the projective-side compression in
both trace orientations.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def orderedDifferencesV97 (set : RawSet) : List Nat :=
  set.flatMap fun left =>
    set.map fun right => (left.val + 36 - right.val) % 36

def orderedDifferenceBilinearV97 (left right : RawSet) : Int :=
  (orderedDifferencesV97 left |>.map fun outer =>
    (orderedDifferencesV97 right |>.map fun inner =>
      zetaScalarZeroV89 (outer * inner)).sum).sum

private theorem sum_map_sum_swap_v97
    (left right : List Nat) (f : Nat → Nat → Int) :
    (left.map fun x => (right.map fun y => f x y).sum).sum =
      (right.map fun y => (left.map fun x => f x y).sum).sum := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [List.sum_map_add]
      /-
      have hadd :
          (right.map fun y => f head y).sum +
              (right.map fun y =>
                (tail.map fun x => f x y).sum).sum =
            (right.map fun y =>
              f head y + (tail.map fun x => f x y).sum).sum := by
        induction right with
        | nil => simp
        | cons next rest ihRight =>
            simp only [List.map_cons, List.sum_cons] at ihRight ⊢
            abel
      exact hadd
      -/

theorem gramTraceScalarZeroV89_eq_orderedDifferenceBilinear_v97
    (left right : RawSet) :
    gramTraceScalarZeroV89 left right =
      orderedDifferenceBilinearV97 left right := by
  unfold gramTraceScalarZeroV89 energyScalarZeroV89
    orderedDifferenceBilinearV97 orderedDifferencesV97
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem orderedDifferenceBilinearV97_comm (left right : RawSet) :
    orderedDifferenceBilinearV97 left right =
      orderedDifferenceBilinearV97 right left := by
  unfold orderedDifferenceBilinearV97
  rw [sum_map_sum_swap_v97]
  apply congrArg List.sum
  apply List.map_congr_left
  intro inner _hinner
  apply congrArg List.sum
  apply List.map_congr_left
  intro outer _houter
  rw [Nat.mul_comm]

theorem gramTraceScalarZeroV89_comm_v97 (left right : RawSet) :
    gramTraceScalarZeroV89 left right =
      gramTraceScalarZeroV89 right left := by
  rw [gramTraceScalarZeroV89_eq_orderedDifferenceBilinear_v97,
    gramTraceScalarZeroV89_eq_orderedDifferenceBilinear_v97,
    orderedDifferenceBilinearV97_comm]

#print axioms gramTraceScalarZeroV89_eq_orderedDifferenceBilinear_v97
#print axioms gramTraceScalarZeroV89_comm_v97

end Fuglede.Z180K30ExceptionalRawV2
