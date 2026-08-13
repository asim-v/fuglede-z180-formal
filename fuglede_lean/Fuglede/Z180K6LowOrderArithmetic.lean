import Mathlib.Tactic

/-!
# Small arithmetic kernels for the low-order branch at cardinality six

The set-level normal form has four projected points in one residue class
modulo six and one point in each adjacent class.  This file records that
pattern abstractly for a vector of thirty-six integral occupancies and proves
the first concrete incompatibility: a primitive ninth-root zero is
impossible.  Polynomial-to-remainder adapters live in a separate module.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- Sum of a thirty-six-coordinate vector over one residue class modulo six.
The explicit six-way table keeps downstream Presburger certificates small. -/
def z180K6ResidueSixSum (b : Fin 36 → Int) (r : ZMod 6) : Int :=
  match r.val with
  | 0 => b 0 + b 6 + b 12 + b 18 + b 24 + b 30
  | 1 => b 1 + b 7 + b 13 + b 19 + b 25 + b 31
  | 2 => b 2 + b 8 + b 14 + b 20 + b 26 + b 32
  | 3 => b 3 + b 9 + b 15 + b 21 + b 27 + b 33
  | 4 => b 4 + b 10 + b 16 + b 22 + b 28 + b 34
  | _ => b 5 + b 11 + b 17 + b 23 + b 29 + b 35

/-- The `(4,1,1)` residue pattern.  The six disjuncts are its six rotations;
this explicit form is intentionally friendly to small linear certificates. -/
def Z180K6ResidueSixPattern (b : Fin 36 → Int) : Prop :=
  let r0 := b 0 + b 6 + b 12 + b 18 + b 24 + b 30
  let r1 := b 1 + b 7 + b 13 + b 19 + b 25 + b 31
  let r2 := b 2 + b 8 + b 14 + b 20 + b 26 + b 32
  let r3 := b 3 + b 9 + b 15 + b 21 + b 27 + b 33
  let r4 := b 4 + b 10 + b 16 + b 22 + b 28 + b 34
  let r5 := b 5 + b 11 + b 17 + b 23 + b 29 + b 35
  (r0 = 4 ∧ r1 = 1 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 1) ∨
  (r0 = 1 ∧ r1 = 4 ∧ r2 = 1 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 0) ∨
  (r0 = 0 ∧ r1 = 1 ∧ r2 = 4 ∧ r3 = 1 ∧ r4 = 0 ∧ r5 = 0) ∨
  (r0 = 0 ∧ r1 = 0 ∧ r2 = 1 ∧ r3 = 4 ∧ r4 = 1 ∧ r5 = 0) ∨
  (r0 = 0 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 1 ∧ r4 = 4 ∧ r5 = 1) ∨
  (r0 = 1 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 1 ∧ r5 = 4)

/-- A primitive second-root zero would balance the two parity classes, which
the `(4,1,1)` pattern does not. -/
theorem z180_k6_phi2_remainder_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (hrem :
      b 0 - b 1 + b 2 - b 3 + b 4 - b 5 +
      b 6 - b 7 + b 8 - b 9 + b 10 - b 11 +
      b 12 - b 13 + b 14 - b 15 + b 16 - b 17 +
      b 18 - b 19 + b 20 - b 21 + b 22 - b 23 +
      b 24 - b 25 + b 26 - b 27 + b 28 - b 29 +
      b 30 - b 31 + b 32 - b 33 + b 34 - b 35 = 0) :
    False := by
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

/-- The two primitive-third-root remainder equations force equal total
occupancy in the three residue classes modulo three; the normal form has
class sizes `(4,1,1)`. -/
theorem z180_k6_phi3_remainders_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (h0 :
      b 0 + b 3 + b 6 + b 9 + b 12 + b 15 +
      b 18 + b 21 + b 24 + b 27 + b 30 + b 33 -
      (b 2 + b 5 + b 8 + b 11 + b 14 + b 17 +
        b 20 + b 23 + b 26 + b 29 + b 32 + b 35) = 0)
    (h1 :
      b 1 + b 4 + b 7 + b 10 + b 13 + b 16 +
      b 19 + b 22 + b 25 + b 28 + b 31 + b 34 -
      (b 2 + b 5 + b 8 + b 11 + b 14 + b 17 +
        b 20 + b 23 + b 26 + b 29 + b 32 + b 35) = 0) :
    False := by
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

/-- The six integral remainder equations for divisibility by `Phi_9` are
incompatible with the cardinality-six `(4,1,1)` pattern modulo six. -/
theorem z180_k6_phi9_remainders_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (h0 : b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33 = 0)
    (h1 : b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34 = 0)
    (h2 : b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35 = 0)
    (h3 : b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33 = 0)
    (h4 : b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34 = 0)
    (h5 : b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35 = 0) :
    False := by
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

#print axioms z180_k6_phi9_remainders_impossible
#print axioms z180_k6_phi2_remainder_impossible
#print axioms z180_k6_phi3_remainders_impossible

end Fuglede
