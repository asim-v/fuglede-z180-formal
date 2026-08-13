import Fuglede.Z180ExactOrderTransform

/-!
# Exact interfaces for the three mixed cardinality-twelve descent orders

The deterministic meet-in-the-middle transcript with payload SHA-256

`7b7af9e3916f9bc578753d9d1e6cfd5748611d78e18aec3a23201d79506f6286`

excludes the base orders `12`, `18`, and `36` in a five-factor defect.  This
module does not trust that transcript.  It names the three propositions that
future kernel-checked finite certificates must prove, and supplies the exact
assembly used by the semantic descent.  The source evidence reports:

* order 12: 75 normalized cases and 8,303 DFS nodes;
* order 18: 77 normalized cases and 435 DFS nodes;
* order 36: 79 normalized cases and 82 DFS nodes.

Keeping the interfaces at set level lets each finite kernel choose its own
sharding and normalization proof without changing the downstream theorem.
-/

namespace Fuglede

open Polynomial

/-- Exact semantic endpoint for one proposed base order in the
cardinality-twelve five-factor descent.  The order-two and order-four
transform equations are the unconditional spectral inputs; their conversion
to cyclotomic mask divisors is already kernel-checked elsewhere. -/
def Z180K12DescentOrderKernel (m : Nat) : Prop :=
  ∀ A : Finset (ZMod 180),
    A.card = 12 →
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) →
    z180ExactOrderTransform A 2 = 0 →
    z180ExactOrderTransform A 4 = 0 →
    cyclotomic (m * 5) Int ∣ maskPolynomial 180 A →
    (¬ cyclotomic m Int ∣ maskPolynomial 180 A) →
    False

/-- Kernel interface for the 75 normalized order-twelve cases. -/
def Z180K12DescentOrder12Kernel : Prop :=
  Z180K12DescentOrderKernel 12

/-- Kernel interface for the 77 normalized order-eighteen cases. -/
def Z180K12DescentOrder18Kernel : Prop :=
  Z180K12DescentOrderKernel 18

/-- Kernel interface for the 79 normalized order-thirty-six cases. -/
def Z180K12DescentOrder36Kernel : Prop :=
  Z180K12DescentOrderKernel 36

/-- The three independent finite certificates, packaged for the final order
case split. -/
structure Z180K12MixedDescentKernels : Prop where
  order12 : Z180K12DescentOrder12Kernel
  order18 : Z180K12DescentOrder18Kernel
  order36 : Z180K12DescentOrder36Kernel

/-- Assembly of the three exact finite kernels: a five-factor defect cannot
have base order 12, 18, or 36. -/
theorem z180_k12_mixed_descent_order_impossible
    (hkernels : Z180K12MixedDescentKernels)
    {A : Finset (ZMod 180)} {m : Nat}
    (hmixed : m = 12 ∨ m = 18 ∨ m = 36)
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A)
    (hlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A) :
    False := by
  rcases hmixed with rfl | rfl | rfl
  · exact hkernels.order12 A hcard hinj htransform2 htransform4 hhigh hlow
  · exact hkernels.order18 A hcard hinj htransform2 htransform4 hhigh hlow
  · exact hkernels.order36 A hcard hinj htransform2 htransform4 hhigh hlow

/-- Negated-equality form convenient after the divisor-of-36 case split. -/
theorem z180_k12_descent_order_ne_twelve_eighteen_thirtysix
    (hkernels : Z180K12MixedDescentKernels)
    {A : Finset (ZMod 180)} {m : Nat}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A)
    (hlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A) :
    m ≠ 12 ∧ m ≠ 18 ∧ m ≠ 36 := by
  constructor
  · intro hm
    exact z180_k12_mixed_descent_order_impossible hkernels
      (Or.inl hm) hcard hinj htransform2 htransform4 hhigh hlow
  constructor
  · intro hm
    exact z180_k12_mixed_descent_order_impossible hkernels
      (Or.inr (Or.inl hm)) hcard hinj htransform2 htransform4 hhigh hlow
  · intro hm
    exact z180_k12_mixed_descent_order_impossible hkernels
      (Or.inr (Or.inr hm)) hcard hinj htransform2 htransform4 hhigh hlow

#print axioms z180_k12_mixed_descent_order_impossible
#print axioms z180_k12_descent_order_ne_twelve_eighteen_thirtysix

end Fuglede
