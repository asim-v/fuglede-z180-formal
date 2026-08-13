import Fuglede.Z180K18DescentImages
import Mathlib.Tactic

/-!
# Pair fibres for the cardinality-eighteen `m = 12` branch

This is block A of the table-free `m = 12` reduction.  It packages the
eighteen points as nine pairs indexed by their residue modulo nine.  The two
members of each pair lie in one fifth-coordinate level and their projected
difference has order four, which is the intrinsic form of opposite parity in
the four-point kernel of `ZMod 36 -> ZMod 9`.

The remaining extraction from the five cyclotomic divisors is exposed as a
two-field interface.  No inhabitant of that interface is asserted here:
the low-order field must prove that every modulo-nine fibre has cardinality
two, and the high-order field must derive the same-level/order-four geometry
from `Phi_10`, `Phi_30`, and `Phi_90`.  Everything after those two precise
facts is proved below.  This module does not use `Phi_60`, choose a normalized
twelfth-root phase, or assert the terminal semantic contradiction.
-/

namespace Fuglede

open Polynomial

/-- The points of `A` in one residue class modulo nine. -/
def z180K18M12NineFiber (A : Finset (ZMod 180)) (r : ZMod 9) :
    Finset (ZMod 180) :=
  A.filter fun x => (ZMod.cast x : ZMod 9) = r

/-- Exact low-order conclusion needed by the pair construction. -/
def Z180K18M12NineFibresHaveCardTwo (A : Finset (ZMod 180)) : Prop :=
  ∀ r : ZMod 9, (z180K18M12NineFiber A r).card = 2

/-- Exact high-order geometric conclusion needed by the pair construction. -/
def Z180K18M12PairGeometry (A : Finset (ZMod 180)) : Prop :=
  ∀ r : ZMod 9, ∀ x ∈ z180K18M12NineFiber A r,
    ∀ y ∈ z180K18M12NineFiber A r, x ≠ y →
      (ZMod.cast x : ZMod 5) = ZMod.cast y ∧
        frequencyOrder 36
          (z180K18Projection36 x - z180K18Projection36 y) = 4

/-- Nine same-level, opposite-parity pairs which cover `A` exactly.  The
fibre equality makes the coverage and residue labels canonical without
choosing an ordering between the two parities. -/
structure Z180K18M12PairFibres (A : Finset (ZMod 180)) where
  first : ZMod 9 -> ZMod 180
  second : ZMod 9 -> ZMod 180
  level : ZMod 9 -> ZMod 5
  first_ne_second : ∀ r, first r ≠ second r
  fiber_eq_pair : ∀ r,
    z180K18M12NineFiber A r = {first r, second r}
  first_level : ∀ r, (ZMod.cast (first r) : ZMod 5) = level r
  second_level : ∀ r, (ZMod.cast (second r) : ZMod 5) = level r
  projected_pair_order : ∀ r,
    frequencyOrder 36
      (z180K18Projection36 (first r) - z180K18Projection36 (second r)) = 4

theorem Z180K18M12PairFibres.first_mem
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    p.first r ∈ A := by
  have hmem : p.first r ∈ z180K18M12NineFiber A r := by
    rw [p.fiber_eq_pair r]
    simp
  exact (Finset.mem_filter.mp hmem).1

theorem Z180K18M12PairFibres.second_mem
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    p.second r ∈ A := by
  have hmem : p.second r ∈ z180K18M12NineFiber A r := by
    rw [p.fiber_eq_pair r]
    simp
  exact (Finset.mem_filter.mp hmem).1

theorem Z180K18M12PairFibres.first_cast_nine
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (p.first r) : ZMod 9) = r := by
  have hmem : p.first r ∈ z180K18M12NineFiber A r := by
    rw [p.fiber_eq_pair r]
    simp
  exact (Finset.mem_filter.mp hmem).2

theorem Z180K18M12PairFibres.second_cast_nine
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (p.second r) : ZMod 9) = r := by
  have hmem : p.second r ∈ z180K18M12NineFiber A r := by
    rw [p.fiber_eq_pair r]
    simp
  exact (Finset.mem_filter.mp hmem).2

/-- Every point belongs to the pair carrying its own residue modulo nine. -/
theorem Z180K18M12PairFibres.cover
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    {x : ZMod 180} (hx : x ∈ A) :
    ∃ r : ZMod 9, x = p.first r ∨ x = p.second r := by
  let r : ZMod 9 := ZMod.cast x
  have hmem : x ∈ z180K18M12NineFiber A r := by
    simp [z180K18M12NineFiber, r, hx]
  rw [p.fiber_eq_pair r] at hmem
  exact ⟨r, by simpa using hmem⟩

/-- Once the two exact extraction facts are available, the nine-pair record
is obtained without any further Fourier or finite-table argument. -/
theorem z180_k18_m12_pairFibres_of_card_two_and_geometry
    {A : Finset (ZMod 180)}
    (htwo : Z180K18M12NineFibresHaveCardTwo A)
    (hgeom : Z180K18M12PairGeometry A) :
    Nonempty (Z180K18M12PairFibres A) := by
  classical
  have hexists : ∀ r : ZMod 9,
      ∃ x y : ZMod 180, x ≠ y ∧
        z180K18M12NineFiber A r = {x, y} := by
    intro r
    exact Finset.card_eq_two.mp (htwo r)
  choose first second hne hfiber using hexists
  have hfirst : ∀ r, first r ∈ z180K18M12NineFiber A r := by
    intro r
    rw [hfiber r]
    simp
  have hsecond : ∀ r, second r ∈ z180K18M12NineFiber A r := by
    intro r
    rw [hfiber r]
    simp
  refine ⟨{
    first := first
    second := second
    level := fun r => (ZMod.cast (first r) : ZMod 5)
    first_ne_second := hne
    fiber_eq_pair := hfiber
    first_level := by intro r; rfl
    second_level := ?_
    projected_pair_order := ?_
  }⟩
  · intro r
    exact (hgeom r (first r) (hfirst r) (second r) (hsecond r) (hne r)).1.symm
  · intro r
    exact (hgeom r (first r) (hfirst r) (second r) (hsecond r) (hne r)).2

/-- Honest boundary for the still-unproved cyclotomic-to-pair extraction.
Its two fields deliberately separate the elementary `Phi_3`/`Phi_9`
equidistribution from the `Phi_10`/`Phi_30`/`Phi_90` parity geometry. -/
structure Z180K18M12PairFibresExtractionInterface where
  low_order_fibres :
    ∀ (A : Finset (ZMod 180)), A.card = 18 →
      cyclotomic 3 Int ∣ maskPolynomial 180 A →
      cyclotomic 9 Int ∣ maskPolynomial 180 A →
      Z180K18M12NineFibresHaveCardTwo A
  high_order_geometry :
    ∀ (A : Finset (ZMod 180)),
      Set.InjOn z180K18Projection36 (A : Set (ZMod 180)) →
      cyclotomic 10 Int ∣ maskPolynomial 180 A →
      cyclotomic 30 Int ∣ maskPolynomial 180 A →
      cyclotomic 90 Int ∣ maskPolynomial 180 A →
      Z180K18M12NineFibresHaveCardTwo A →
      Z180K18M12PairGeometry A

/-- Conditional assembly endpoint with every mathematical input visible.
No theorem in this module supplies `hextract`. -/
theorem z180_k18_m12_pairFibres_of_cyclotomic_profile_of_interface
    (hextract : Z180K18M12PairFibresExtractionInterface)
    {A : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hinj : Set.InjOn z180K18Projection36 (A : Set (ZMod 180)))
    (h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A)
    (h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A)
    (h10 : cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : cyclotomic 90 Int ∣ maskPolynomial 180 A) :
    Nonempty (Z180K18M12PairFibres A) := by
  have htwo := hextract.low_order_fibres A hcard h3 h9
  have hgeom := hextract.high_order_geometry A hinj h10 h30 h90 htwo
  exact z180_k18_m12_pairFibres_of_card_two_and_geometry htwo hgeom

#print axioms z180_k18_m12_pairFibres_of_card_two_and_geometry
#print axioms z180_k18_m12_pairFibres_of_cyclotomic_profile_of_interface

end Fuglede
