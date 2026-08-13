import Mathlib.Tactic

/-!
# Small Presburger kernel for the order-twenty branch

The five fibres modulo five all have vanishing `Phi_4` remainder and a
common, nonzero `Phi_6` remainder.  At total cardinality twelve their sizes
are therefore `2,2,2,2,4`.  Comparing any size-two fibre with the size-four
fibre forces complementary parity profiles; four such comparisons contradict
the global profile `(3,3,3,3)`.

This file contains only the finite integral arithmetic.  The set-level
adapter is kept in a separate module.
-/

namespace Fuglede

set_option maxHeartbeats 0

def z180K12Order20Mass (a : Fin 12 → Int) : Int :=
  a 0 + a 1 + a 2 + a 3 + a 4 + a 5 +
    a 6 + a 7 + a 8 + a 9 + a 10 + a 11

def z180K12Order20P0 (a : Fin 12 → Int) : Int :=
  a 0 + a 4 + a 8

def z180K12Order20P1 (a : Fin 12 → Int) : Int :=
  a 1 + a 5 + a 9

def z180K12Order20P2 (a : Fin 12 → Int) : Int :=
  a 2 + a 6 + a 10

def z180K12Order20P3 (a : Fin 12 → Int) : Int :=
  a 3 + a 7 + a 11

def z180K12Order20Phi4R0 (a : Fin 12 → Int) : Int :=
  a 0 - a 2 + a 4 - a 6 + a 8 - a 10

def z180K12Order20Phi4R1 (a : Fin 12 → Int) : Int :=
  a 1 - a 3 + a 5 - a 7 + a 9 - a 11

def z180K12Order20Phi6R0 (a : Fin 12 → Int) : Int :=
  a 0 - a 2 - a 3 + a 5 + a 6 - a 8 - a 9 + a 11

def z180K12Order20Phi6R1 (a : Fin 12 → Int) : Int :=
  a 1 + a 2 - a 4 - a 5 + a 7 + a 8 - a 10 - a 11

def z180K12Order20ParityDifference (a : Fin 12 → Int) : Int :=
  z180K12Order20P0 a + z180K12Order20P2 a -
    z180K12Order20P1 a - z180K12Order20P3 a

private def z180K12Order20Phi6CongruenceWitness
    (a : Fin 12 → Int) : Int :=
  a 2 - a 5 + a 8 - a 11

private theorem order20_parity_difference_identity (a : Fin 12 → Int) :
    z180K12Order20ParityDifference a =
      (z180K12Order20Phi6R0 a - z180K12Order20Phi6R1 a) +
        3 * z180K12Order20Phi6CongruenceWitness a := by
  dsimp only [z180K12Order20ParityDifference,
    z180K12Order20Phi6R0, z180K12Order20Phi6R1,
    z180K12Order20Phi6CongruenceWitness, z180K12Order20P0,
    z180K12Order20P1, z180K12Order20P2, z180K12Order20P3]
  ring

private theorem order20_small_profile_cases
    (p0 p1 p2 p3 : Int)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2) (h3 : 0 ≤ p3)
    (hmass : p0 + p1 + p2 + p3 = 2)
    (heven : p0 = p2) (hodd : p1 = p3) :
    (p0 = 1 ∧ p1 = 0 ∧ p2 = 1 ∧ p3 = 0) ∨
      (p0 = 0 ∧ p1 = 1 ∧ p2 = 0 ∧ p3 = 1) := by
  omega

private theorem order20_large_profile_cases
    (p0 p1 p2 p3 : Int)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2) (h3 : 0 ≤ p3)
    (hmass : p0 + p1 + p2 + p3 = 4)
    (heven : p0 = p2) (hodd : p1 = p3) :
    (p0 = 2 ∧ p1 = 0 ∧ p2 = 2 ∧ p3 = 0) ∨
    (p0 = 1 ∧ p1 = 1 ∧ p2 = 1 ∧ p3 = 1) ∨
    (p0 = 0 ∧ p1 = 2 ∧ p2 = 0 ∧ p3 = 2) := by
  omega

/-- The two possible mod-four profiles of a size-two fibre, together with
the forced complementary profile of a size-four fibre. -/
def Z180K12Order20SmallLargeShape
    (small large : Fin 12 → Int) : Prop :=
  (z180K12Order20P0 small = 1 ∧
      z180K12Order20P1 small = 0 ∧
      z180K12Order20P2 small = 1 ∧
      z180K12Order20P3 small = 0 ∧
      z180K12Order20P0 large = 0 ∧
      z180K12Order20P1 large = 2 ∧
      z180K12Order20P2 large = 0 ∧
      z180K12Order20P3 large = 2) ∨
    (z180K12Order20P0 small = 0 ∧
      z180K12Order20P1 small = 1 ∧
      z180K12Order20P2 small = 0 ∧
      z180K12Order20P3 small = 1 ∧
      z180K12Order20P0 large = 2 ∧
      z180K12Order20P1 large = 0 ∧
      z180K12Order20P2 large = 2 ∧
      z180K12Order20P3 large = 0)

/-- Exact two-versus-four classification.  Notice that no upper bound is
needed: nonnegativity, the two masses, `Phi_4 = 0`, and equality of the two
`Phi_6` remainders already determine both profiles. -/
theorem z180_k12_order20_small_large_shape
    (small large : Fin 12 → Int)
    (hsmall : ∀ r, 0 ≤ small r)
    (hlarge : ∀ r, 0 ≤ large r)
    (hsmallMass : z180K12Order20Mass small = 2)
    (hlargeMass : z180K12Order20Mass large = 4)
    (hsmall40 : z180K12Order20Phi4R0 small = 0)
    (hsmall41 : z180K12Order20Phi4R1 small = 0)
    (hlarge40 : z180K12Order20Phi4R0 large = 0)
    (hlarge41 : z180K12Order20Phi4R1 large = 0)
    (hphi60 : z180K12Order20Phi6R0 small =
      z180K12Order20Phi6R0 large)
    (hphi61 : z180K12Order20Phi6R1 small =
      z180K12Order20Phi6R1 large) :
    Z180K12Order20SmallLargeShape small large := by
  have hsP0 : 0 ≤ z180K12Order20P0 small := by
    exact add_nonneg (add_nonneg (hsmall 0) (hsmall 4)) (hsmall 8)
  have hsP1 : 0 ≤ z180K12Order20P1 small := by
    exact add_nonneg (add_nonneg (hsmall 1) (hsmall 5)) (hsmall 9)
  have hsP2 : 0 ≤ z180K12Order20P2 small := by
    exact add_nonneg (add_nonneg (hsmall 2) (hsmall 6)) (hsmall 10)
  have hsP3 : 0 ≤ z180K12Order20P3 small := by
    exact add_nonneg (add_nonneg (hsmall 3) (hsmall 7)) (hsmall 11)
  have hlP0 : 0 ≤ z180K12Order20P0 large := by
    exact add_nonneg (add_nonneg (hlarge 0) (hlarge 4)) (hlarge 8)
  have hlP1 : 0 ≤ z180K12Order20P1 large := by
    exact add_nonneg (add_nonneg (hlarge 1) (hlarge 5)) (hlarge 9)
  have hlP2 : 0 ≤ z180K12Order20P2 large := by
    exact add_nonneg (add_nonneg (hlarge 2) (hlarge 6)) (hlarge 10)
  have hlP3 : 0 ≤ z180K12Order20P3 large := by
    exact add_nonneg (add_nonneg (hlarge 3) (hlarge 7)) (hlarge 11)
  have hsMassProfile :
      z180K12Order20P0 small + z180K12Order20P1 small +
          z180K12Order20P2 small + z180K12Order20P3 small = 2 := by
    rw [← hsmallMass]
    dsimp only [z180K12Order20Mass, z180K12Order20P0,
      z180K12Order20P1, z180K12Order20P2, z180K12Order20P3]
    ring
  have hlMassProfile :
      z180K12Order20P0 large + z180K12Order20P1 large +
          z180K12Order20P2 large + z180K12Order20P3 large = 4 := by
    rw [← hlargeMass]
    dsimp only [z180K12Order20Mass, z180K12Order20P0,
      z180K12Order20P1, z180K12Order20P2, z180K12Order20P3]
    ring
  have hsEven : z180K12Order20P0 small = z180K12Order20P2 small := by
    dsimp only [z180K12Order20Phi4R0, z180K12Order20P0,
      z180K12Order20P2] at hsmall40 ⊢
    linarith only [hsmall40]
  have hsOdd : z180K12Order20P1 small = z180K12Order20P3 small := by
    dsimp only [z180K12Order20Phi4R1, z180K12Order20P1,
      z180K12Order20P3] at hsmall41 ⊢
    linarith only [hsmall41]
  have hlEven : z180K12Order20P0 large = z180K12Order20P2 large := by
    dsimp only [z180K12Order20Phi4R0, z180K12Order20P0,
      z180K12Order20P2] at hlarge40 ⊢
    linarith only [hlarge40]
  have hlOdd : z180K12Order20P1 large = z180K12Order20P3 large := by
    dsimp only [z180K12Order20Phi4R1, z180K12Order20P1,
      z180K12Order20P3] at hlarge41 ⊢
    linarith only [hlarge41]
  have hsCases := order20_small_profile_cases
    (z180K12Order20P0 small) (z180K12Order20P1 small)
    (z180K12Order20P2 small) (z180K12Order20P3 small)
    hsP0 hsP1 hsP2 hsP3 hsMassProfile hsEven hsOdd
  have hlCases := order20_large_profile_cases
    (z180K12Order20P0 large) (z180K12Order20P1 large)
    (z180K12Order20P2 large) (z180K12Order20P3 large)
    hlP0 hlP1 hlP2 hlP3 hlMassProfile hlEven hlOdd
  have hcongruence : ∃ k : Int,
      z180K12Order20ParityDifference large -
          z180K12Order20ParityDifference small = 3 * k := by
    refine ⟨z180K12Order20Phi6CongruenceWitness large -
      z180K12Order20Phi6CongruenceWitness small, ?_⟩
    rw [order20_parity_difference_identity,
      order20_parity_difference_identity, hphi60, hphi61]
    ring
  obtain ⟨k, hk⟩ := hcongruence
  dsimp only [z180K12Order20ParityDifference] at hk
  rcases hsCases with hsCases | hsCases <;>
    rcases hlCases with hlCases | hlCases | hlCases <;>
    dsimp only [Z180K12Order20SmallLargeShape] <;>
    omega

/-- Five positive even integers summing to twelve consist of one four and
four twos. -/
theorem z180_k12_order20_five_masses
    (s0 s1 s2 s3 s4 : Int)
    (hpos0 : 1 ≤ s0) (hpos1 : 1 ≤ s1) (hpos2 : 1 ≤ s2)
    (hpos3 : 1 ≤ s3) (hpos4 : 1 ≤ s4)
    (heven0 : ∃ t : Int, s0 = 2 * t)
    (heven1 : ∃ t : Int, s1 = 2 * t)
    (heven2 : ∃ t : Int, s2 = 2 * t)
    (heven3 : ∃ t : Int, s3 = 2 * t)
    (heven4 : ∃ t : Int, s4 = 2 * t)
    (hsum : s0 + s1 + s2 + s3 + s4 = 12) :
    (s0 = 4 ∧ s1 = 2 ∧ s2 = 2 ∧ s3 = 2 ∧ s4 = 2) ∨
    (s0 = 2 ∧ s1 = 4 ∧ s2 = 2 ∧ s3 = 2 ∧ s4 = 2) ∨
    (s0 = 2 ∧ s1 = 2 ∧ s2 = 4 ∧ s3 = 2 ∧ s4 = 2) ∨
    (s0 = 2 ∧ s1 = 2 ∧ s2 = 2 ∧ s3 = 4 ∧ s4 = 2) ∨
    (s0 = 2 ∧ s1 = 2 ∧ s2 = 2 ∧ s3 = 2 ∧ s4 = 4) := by
  obtain ⟨t0, ht0⟩ := heven0
  obtain ⟨t1, ht1⟩ := heven1
  obtain ⟨t2, ht2⟩ := heven2
  obtain ⟨t3, ht3⟩ := heven3
  obtain ⟨t4, ht4⟩ := heven4
  omega

/-- Vanishing of the two `Phi_4` remainders makes the mass even. -/
theorem z180_k12_order20_mass_even_of_phi4
    (a : Fin 12 → Int)
    (h40 : z180K12Order20Phi4R0 a = 0)
    (h41 : z180K12Order20Phi4R1 a = 0) :
    ∃ t : Int, z180K12Order20Mass a = 2 * t := by
  refine ⟨z180K12Order20P0 a + z180K12Order20P1 a, ?_⟩
  dsimp only [z180K12Order20Mass, z180K12Order20Phi4R0,
    z180K12Order20Phi4R1, z180K12Order20P0,
    z180K12Order20P1] at h40 h41 ⊢
  linarith only [h40, h41]

/-- Four small profiles cannot all be complementary to one large profile
while their coordinatewise total is `(3,3,3,3)`. -/
theorem z180_k12_order20_four_small_profiles_impossible
    (s0 s1 s2 s3 large : Fin 12 → Int)
    (h0 : Z180K12Order20SmallLargeShape s0 large)
    (h1 : Z180K12Order20SmallLargeShape s1 large)
    (h2 : Z180K12Order20SmallLargeShape s2 large)
    (h3 : Z180K12Order20SmallLargeShape s3 large)
    (hp0 : z180K12Order20P0 s0 + z180K12Order20P0 s1 +
        z180K12Order20P0 s2 + z180K12Order20P0 s3 +
        z180K12Order20P0 large = 3)
    (hp1 : z180K12Order20P1 s0 + z180K12Order20P1 s1 +
        z180K12Order20P1 s2 + z180K12Order20P1 s3 +
        z180K12Order20P1 large = 3)
    (hp2 : z180K12Order20P2 s0 + z180K12Order20P2 s1 +
        z180K12Order20P2 s2 + z180K12Order20P2 s3 +
        z180K12Order20P2 large = 3)
    (hp3 : z180K12Order20P3 s0 + z180K12Order20P3 s1 +
        z180K12Order20P3 s2 + z180K12Order20P3 s3 +
        z180K12Order20P3 large = 3) : False := by
  rcases h0 with h0 | h0
  · have hs1 : z180K12Order20P0 s1 = 1 := by
      rcases h1 with h1 | h1 <;> omega
    have hs2 : z180K12Order20P0 s2 = 1 := by
      rcases h2 with h2 | h2 <;> omega
    have hs3 : z180K12Order20P0 s3 = 1 := by
      rcases h3 with h3 | h3 <;> omega
    omega
  · have hs1 : z180K12Order20P0 s1 = 0 := by
      rcases h1 with h1 | h1 <;> omega
    have hs2 : z180K12Order20P0 s2 = 0 := by
      rcases h2 with h2 | h2 <;> omega
    have hs3 : z180K12Order20P0 s3 = 0 := by
      rcases h3 with h3 | h3 <;> omega
    omega

#print axioms z180_k12_order20_small_large_shape
#print axioms z180_k12_order20_five_masses
#print axioms z180_k12_order20_mass_even_of_phi4
#print axioms z180_k12_order20_four_small_profiles_impossible

end Fuglede
