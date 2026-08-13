import Fuglede.Z180K12GraphDefs
import Mathlib.Tactic

/-!
# Kernel-reduced terminal graph for the `ZMod 180`, `k = 12` branch

This module reproves the two finite leaves of `Z180K12Graph` with ordinary
kernel reduction (`decide`) and threads only those new leaves through the
structural clique argument.  Consequently the endpoint below does not depend
on any code-generation shortcut or generated checker assumption.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Kernel-reduced version of the normalized cross-level triangle check. -/
theorem z180_k12_cross_triangle_endpoint_kernel :
    ∀ a b : ZMod 180,
      Z180K12AllowedDifference a → z180K12Fifth a ≠ 0 →
      Z180K12AllowedDifference b →
      Z180K12AllowedDifference (a - b) → b = a := by
  decide

/-- Kernel-reduced version of the finite six-colouring check. -/
theorem z180_k12_color_shift_ne_kernel :
    ∀ r : ZMod 12, ∀ d : ZMod 180,
      Z180K12AllowedDifference d → z180K12Fifth d = 0 →
      z180K12ColorTable (r + ZMod.cast d) ≠ z180K12ColorTable r := by
  decide

/-- Same-fifth compatible vertices receive distinct colours, using only the
kernel-reduced finite leaf above. -/
theorem z180_k12_color_ne_of_same_fifth_kernel (x y : ZMod 180)
    (hallowed : Z180K12AllowedDifference (y - x))
    (hfifth : z180K12Fifth y = z180K12Fifth x) :
    z180K12Color y ≠ z180K12Color x := by
  have hd5 : z180K12Fifth (y - x) = 0 := by
    simp [z180_k12_fifth_sub, hfifth]
  have h := z180_k12_color_shift_ne_kernel (ZMod.cast x : ZMod 12)
    (y - x) hallowed hd5
  simpa [z180K12Color] using h

/-- Any finite set whose nonzero pairwise differences lie in the six-order
envelope has at most six elements.  This proof uses the kernel leaves in this
module, not the native-decision leaves in the imported compatibility module. -/
theorem z180_k12_card_le_six_of_pairwise_allowed_kernel
    (L : Finset (ZMod 180))
    (hpair : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      Z180K12AllowedDifference (x - y)) :
    L.card ≤ 6 := by
  classical
  by_cases hsame : ∀ x ∈ L, ∀ y ∈ L,
      z180K12Fifth x = z180K12Fifth y
  · let color : ↥L → Fin 6 := fun x ↦ z180K12Color x.1
    have hinjective : Function.Injective color := by
      intro x y hcolor
      by_contra hxy
      have hval : x.1 ≠ y.1 := by
        intro h
        apply hxy
        exact Subtype.ext h
      have hallowed := hpair y.1 y.2 x.1 x.2 hval.symm
      have hne := z180_k12_color_ne_of_same_fifth_kernel x.1 y.1
        hallowed (hsame x.1 x.2 y.1 y.2).symm
      exact hne hcolor.symm
    have hcard := Fintype.card_le_of_injective color hinjective
    simpa using hcard
  · push Not at hsame
    obtain ⟨x, hx, y, hy, hxy_fifth⟩ := hsame
    have hxy : y ≠ x := by
      intro h
      subst y
      exact hxy_fifth rfl
    have hyx_allowed := hpair y hy x hx hxy
    have hyx_fifth : z180K12Fifth (y - x) ≠ 0 := by
      rw [z180_k12_fifth_sub, sub_ne_zero]
      exact hxy_fifth.symm
    have hsubset : L ⊆ {x, y} := by
      intro z hz
      by_cases hzx : z = x
      · simp [hzx]
      by_cases hzy : z = y
      · simp [hzy]
      have hzx_allowed := hpair z hz x hx hzx
      have hyz_allowed := hpair y hy z hz (Ne.symm hzy)
      have hab : Z180K12AllowedDifference ((y - x) - (z - x)) := by
        simpa [sub_sub_sub_cancel_right] using hyz_allowed
      have hdiff : z - x = y - x :=
        z180_k12_cross_triangle_endpoint_kernel (y - x) (z - x)
          hyx_allowed hyx_fifth hzx_allowed hab
      have : z = y := sub_left_injective hdiff
      exact (hzy this).elim
    calc
      L.card ≤ ({x, y} : Finset (ZMod 180)).card :=
        Finset.card_le_card hsubset
      _ ≤ 6 := Finset.card_le_two.trans (by norm_num)

/-- A spectrum whose zero orders lie in the six-order envelope has at most
six frequencies. -/
theorem z180_k12_spectrum_card_le_six_kernel
    (A L : Finset (ZMod 180))
    (hSpec : CyclotomicSpectrum 180 A L)
    (hprofile : ∀ d : ZMod 180, d ≠ 0 →
      CyclotomicZero 180 A d → Z180K12AllowedDifference d) :
    L.card ≤ 6 := by
  apply z180_k12_card_le_six_of_pairwise_allowed_kernel L
  intro x hx y hy hxy
  apply hprofile (x - y) (sub_ne_zero.mpr hxy)
  exact hSpec.2.2 x hx y hy hxy

/-- The six-order zero envelope cannot support a twelve-point spectrum. -/
theorem z180_k12_no_twelve_point_spectrum_kernel
    (A L : Finset (ZMod 180))
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : L.card = 12)
    (hprofile : ∀ d : ZMod 180, d ≠ 0 →
      CyclotomicZero 180 A d → Z180K12AllowedDifference d) : False := by
  have hle := z180_k12_spectrum_card_le_six_kernel A L hSpec hprofile
  omega

#print axioms z180_k12_cross_triangle_endpoint_kernel
#print axioms z180_k12_color_shift_ne_kernel
#print axioms z180_k12_card_le_six_of_pairwise_allowed_kernel
#print axioms z180_k12_no_twelve_point_spectrum_kernel

end Fuglede
