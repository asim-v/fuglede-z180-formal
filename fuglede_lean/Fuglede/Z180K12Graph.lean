import Fuglede.Z180K12GraphDefs
import Mathlib.Tactic

/-!
# The terminal compatibility graph in the `ZMod 180`, `k = 12` branch

The exact branch computation leaves the possible nonzero difference orders

`{2, 4, 9, 10, 30, 36}`.

This module proves that the associated Cayley graph has clique number at most
six, so in particular it cannot support a twelve-point spectrum.  The proof
uses two small, axiom-audited `native_decide` leaves and a structural split
over the `ZMod 5` coordinate:

* a clique meeting two fifth-coordinate levels has at most two vertices;
* a clique in one level injects into an explicit six-colouring depending on
  the `ZMod 12` coordinate.
-/

namespace Fuglede

/-- A normalized compatible triangle containing a cross-level edge has no
third vertex. -/
theorem z180_k12_cross_triangle_endpoint :
    ∀ a b : ZMod 180,
      Z180K12AllowedDifference a → z180K12Fifth a ≠ 0 →
      Z180K12AllowedDifference b →
      Z180K12AllowedDifference (a - b) → b = a := by
  native_decide

/-- Every allowed difference inside one fifth-coordinate level changes the
colour.  This finite check has only `12 × 21` relevant inputs. -/
theorem z180_k12_color_shift_ne :
    ∀ r : ZMod 12, ∀ d : ZMod 180,
      Z180K12AllowedDifference d → z180K12Fifth d = 0 →
      z180K12ColorTable (r + ZMod.cast d) ≠ z180K12ColorTable r := by
  native_decide

/-- Two compatible vertices in one fifth-coordinate level receive distinct
colours. -/
theorem z180_k12_color_ne_of_same_fifth (x y : ZMod 180)
    (hallowed : Z180K12AllowedDifference (y - x))
    (hfifth : z180K12Fifth y = z180K12Fifth x) :
    z180K12Color y ≠ z180K12Color x := by
  have hd5 : z180K12Fifth (y - x) = 0 := by
    simp [z180_k12_fifth_sub, hfifth]
  have h := z180_k12_color_shift_ne (ZMod.cast x : ZMod 12)
    (y - x) hallowed hd5
  simpa [z180K12Color] using h

/-- Main endpoint: any finite set whose nonzero pairwise differences have
orders in `{2,4,9,10,30,36}` has at most six elements. -/
theorem z180_k12_card_le_six_of_pairwise_allowed
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
      have hne := z180_k12_color_ne_of_same_fifth x.1 y.1
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
        z180_k12_cross_triangle_endpoint (y - x) (z - x)
          hyx_allowed hyx_fifth hzx_allowed hab
      have : z = y := sub_left_injective hdiff
      exact (hzy this).elim
    calc
      L.card ≤ ({x, y} : Finset (ZMod 180)).card :=
        Finset.card_le_card hsubset
      _ ≤ 6 := Finset.card_le_two.trans (by norm_num)

/-- Seven pairwise-compatible distinct points cannot exist. -/
theorem z180_k12_no_seven_clique
    (L : Finset (ZMod 180))
    (hcard : L.card = 7)
    (hpair : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      Z180K12AllowedDifference (x - y)) : False := by
  have hle := z180_k12_card_le_six_of_pairwise_allowed L hpair
  omega

/-- Adapter for a cyclotomic spectrum whose realized nonzero zero orders are
contained in the six-order compatibility profile. -/
theorem z180_k12_spectrum_card_le_six
    (A L : Finset (ZMod 180))
    (hspec : CyclotomicSpectrum 180 A L)
    (hprofile : ∀ d : ZMod 180, d ≠ 0 →
      CyclotomicZero 180 A d → Z180K12AllowedDifference d) :
    L.card ≤ 6 := by
  apply z180_k12_card_le_six_of_pairwise_allowed L
  intro x hx y hy hxy
  apply hprofile (x - y) (sub_ne_zero.mpr hxy)
  exact hspec.2.2 x hx y hy hxy

/-- In particular, the six-order profile cannot occur for a spectrum of
cardinality twelve. -/
theorem z180_k12_no_twelve_point_spectrum
    (A L : Finset (ZMod 180))
    (hspec : CyclotomicSpectrum 180 A L)
    (hcard : L.card = 12)
    (hprofile : ∀ d : ZMod 180, d ≠ 0 →
      CyclotomicZero 180 A d → Z180K12AllowedDifference d) : False := by
  have hle := z180_k12_spectrum_card_le_six A L hspec hprofile
  omega

end Fuglede
