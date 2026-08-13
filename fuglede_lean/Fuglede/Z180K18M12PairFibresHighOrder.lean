import Fuglede.Z180K18M12HighOrderLevels
import Fuglede.Z180K18M12PairFibres
import Mathlib.Tactic

/-!
# Reduced high-order interface for the `k = 18`, `m = 12` pair fibres

The cyclotomic/Fourier part is complete before this module: the alternating
profile of a fifth-coordinate level is independent of the level.  A fibre of
total mass two then forces that common profile to be zero, since five times
an integer cannot lie strictly between `-5` and `5` unless it is zero.

The only residual interface consists of two elementary finite-set adapters:
identifying the four projected occupancies with the cardinality of a
modulo-nine fibre, and reading a zero signed profile on a two-point fibre as
same fifth level plus opposite parity.  No Fourier or cyclotomic premise is
left in that interface.
-/

namespace Fuglede

open scoped BigOperators

set_option maxHeartbeats 0

/-- Total projected mass above one residue modulo nine. -/
def z180K18M12NineFiberMass (b : Fin 36 → Int) (r : ZMod 9) : Int :=
  match r.val with
  | 0 => b 0 + b 9 + b 18 + b 27
  | 1 => b 1 + b 10 + b 19 + b 28
  | 2 => b 2 + b 11 + b 20 + b 29
  | 3 => b 3 + b 12 + b 21 + b 30
  | 4 => b 4 + b 13 + b 22 + b 31
  | 5 => b 5 + b 14 + b 23 + b 32
  | 6 => b 6 + b 15 + b 24 + b 33
  | 7 => b 7 + b 16 + b 25 + b 34
  | _ => b 8 + b 17 + b 26 + b 35

/-- Projection spelling of “every modulo-nine fibre has cardinality two”. -/
def Z180K18M12ProjectionNineFibresHaveMassTwo
    (A : Finset (ZMod 180)) : Prop :=
  ∀ r : ZMod 9,
    z180K18M12NineFiberMass (z180K12ProjectionIndicator A) r = 2

private theorem sum_zmod_five_explicit_k18
    {R : Type*} [AddCommMonoid R] (f : ZMod 5 → R) :
    (∑ c : ZMod 5, f c) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert
    (by decide : (0 : ZMod 5) ∉ ({1, 2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (1 : ZMod 5) ∉ ({2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (2 : ZMod 5) ∉ ({3, 4} : Finset (ZMod 5)))]
  rw [Finset.sum_insert
    (by decide : (3 : ZMod 5) ∉ ({4} : Finset (ZMod 5)))]
  simp [add_assoc]

/-- Four-coordinate arithmetic used independently in each modulo-nine
fibre. -/
private theorem five_equal_four_balance_zero
    (a0 a1 a2 a3 : ZMod 5 → Int) (b0 b1 b2 b3 : Int)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hmass : b0 + b1 + b2 + b3 = 2)
    (hpart0 : (∑ c : ZMod 5, a0 c) = b0)
    (hpart1 : (∑ c : ZMod 5, a1 c) = b1)
    (hpart2 : (∑ c : ZMod 5, a2 c) = b2)
    (hpart3 : (∑ c : ZMod 5, a3 c) = b3)
    (heq : ∀ c c' : ZMod 5,
      a0 c - a1 c + a2 c - a3 c =
        a0 c' - a1 c' + a2 c' - a3 c') :
    ∀ c : ZMod 5, a0 c - a1 c + a2 c - a3 c = 0 := by
  intro c
  have hsum :
      (∑ d : ZMod 5, (a0 d - a1 d + a2 d - a3 d)) =
        b0 - b1 + b2 - b3 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hpart0, hpart1, hpart2, hpart3]
  rw [sum_zmod_five_explicit_k18] at hsum
  have h0 := heq 0 c
  have h1 := heq 1 c
  have h2 := heq 2 c
  have h3 := heq 3 c
  have h4 := heq 4 c
  omega

/-- Sign-reversed form of `five_equal_four_balance_zero`, used on the odd
modulo-nine fibres where the ordinary parity sign starts negative. -/
private theorem five_equal_four_balance_zero_neg
    (a0 a1 a2 a3 : ZMod 5 → Int) (b0 b1 b2 b3 : Int)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hmass : b0 + b1 + b2 + b3 = 2)
    (hpart0 : (∑ c : ZMod 5, a0 c) = b0)
    (hpart1 : (∑ c : ZMod 5, a1 c) = b1)
    (hpart2 : (∑ c : ZMod 5, a2 c) = b2)
    (hpart3 : (∑ c : ZMod 5, a3 c) = b3)
    (heq : ∀ c c' : ZMod 5,
      -a0 c + a1 c - a2 c + a3 c =
        -a0 c' + a1 c' - a2 c' + a3 c') :
    ∀ c : ZMod 5, -a0 c + a1 c - a2 c + a3 c = 0 := by
  intro c
  have heq' : ∀ d d' : ZMod 5,
      a0 d - a1 d + a2 d - a3 d =
        a0 d' - a1 d' + a2 d' - a3 d' := by
    intro d d'
    have h := heq d d'
    linarith only [h]
  have h := five_equal_four_balance_zero a0 a1 a2 a3 b0 b1 b2 b3
    hb0 hb1 hb2 hb3 hmass hpart0 hpart1 hpart2 hpart3 heq' c
  linarith only [h]

/-- Equal signed profiles on all five levels, coordinatewise partition, and
mass two force every level profile to vanish. -/
theorem z180_k18_m12_level_signed_profiles_zero_of_eq_and_mass_two
    (b : Fin 36 → Int) (level : ZMod 5 → Fin 36 → Int)
    (hlo : ∀ i : Fin 36, 0 ≤ b i)
    (hmass : ∀ r : ZMod 9, z180K18M12NineFiberMass b r = 2)
    (hpartition : ∀ i : Fin 36, (∑ c : ZMod 5, level c i) = b i)
    (heq : ∀ c c' : ZMod 5, ∀ r : ZMod 9,
      z180K18M12SignedNineFiber (level c) r =
      z180K18M12SignedNineFiber (level c') r) :
    ∀ c : ZMod 5, ∀ r : ZMod 9,
      z180K18M12SignedNineFiber (level c) r = 0 := by
  have hv1 : ZMod.val (1 : ZMod 9) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 9) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 9) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 9) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 9) = 5 := by decide
  have hv6 : ZMod.val (6 : ZMod 9) = 6 := by decide
  have hv7 : ZMod.val (7 : ZMod 9) = 7 := by decide
  have hv8 : ZMod.val (8 : ZMod 9) = 8 := by decide
  intro c r
  fin_cases r
  · exact five_equal_four_balance_zero
      (fun d => level d 0) (fun d => level d 9)
      (fun d => level d 18) (fun d => level d 27)
      (b 0) (b 9) (b 18) (b 27)
      (hlo 0) (hlo 9) (hlo 18) (hlo 27)
      (by simpa [z180K18M12NineFiberMass] using hmass (0 : ZMod 9))
      (hpartition 0) (hpartition 9) (hpartition 18) (hpartition 27)
      (by intro d d'; simpa [z180K18M12SignedNineFiber] using
        heq d d' (0 : ZMod 9)) c
  · exact five_equal_four_balance_zero_neg
      (fun d => level d 1) (fun d => level d 10)
      (fun d => level d 19) (fun d => level d 28)
      (b 1) (b 10) (b 19) (b 28)
      (hlo 1) (hlo 10) (hlo 19) (hlo 28)
      (by simpa [z180K18M12NineFiberMass, hv1] using hmass (1 : ZMod 9))
      (hpartition 1) (hpartition 10) (hpartition 19) (hpartition 28)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv1] using
        heq d d' (1 : ZMod 9)) c
  · exact five_equal_four_balance_zero
      (fun d => level d 2) (fun d => level d 11)
      (fun d => level d 20) (fun d => level d 29)
      (b 2) (b 11) (b 20) (b 29)
      (hlo 2) (hlo 11) (hlo 20) (hlo 29)
      (by simpa [z180K18M12NineFiberMass, hv2] using hmass (2 : ZMod 9))
      (hpartition 2) (hpartition 11) (hpartition 20) (hpartition 29)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv2] using
        heq d d' (2 : ZMod 9)) c
  · exact five_equal_four_balance_zero_neg
      (fun d => level d 3) (fun d => level d 12)
      (fun d => level d 21) (fun d => level d 30)
      (b 3) (b 12) (b 21) (b 30)
      (hlo 3) (hlo 12) (hlo 21) (hlo 30)
      (by simpa [z180K18M12NineFiberMass, hv3] using hmass (3 : ZMod 9))
      (hpartition 3) (hpartition 12) (hpartition 21) (hpartition 30)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv3] using
        heq d d' (3 : ZMod 9)) c
  · exact five_equal_four_balance_zero
      (fun d => level d 4) (fun d => level d 13)
      (fun d => level d 22) (fun d => level d 31)
      (b 4) (b 13) (b 22) (b 31)
      (hlo 4) (hlo 13) (hlo 22) (hlo 31)
      (by simpa [z180K18M12NineFiberMass, hv4] using hmass (4 : ZMod 9))
      (hpartition 4) (hpartition 13) (hpartition 22) (hpartition 31)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv4] using
        heq d d' (4 : ZMod 9)) c
  · exact five_equal_four_balance_zero_neg
      (fun d => level d 5) (fun d => level d 14)
      (fun d => level d 23) (fun d => level d 32)
      (b 5) (b 14) (b 23) (b 32)
      (hlo 5) (hlo 14) (hlo 23) (hlo 32)
      (by simpa [z180K18M12NineFiberMass, hv5] using hmass (5 : ZMod 9))
      (hpartition 5) (hpartition 14) (hpartition 23) (hpartition 32)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv5] using
        heq d d' (5 : ZMod 9)) c
  · exact five_equal_four_balance_zero
      (fun d => level d 6) (fun d => level d 15)
      (fun d => level d 24) (fun d => level d 33)
      (b 6) (b 15) (b 24) (b 33)
      (hlo 6) (hlo 15) (hlo 24) (hlo 33)
      (by simpa [z180K18M12NineFiberMass, hv6] using hmass (6 : ZMod 9))
      (hpartition 6) (hpartition 15) (hpartition 24) (hpartition 33)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv6] using
        heq d d' (6 : ZMod 9)) c
  · exact five_equal_four_balance_zero_neg
      (fun d => level d 7) (fun d => level d 16)
      (fun d => level d 25) (fun d => level d 34)
      (b 7) (b 16) (b 25) (b 34)
      (hlo 7) (hlo 16) (hlo 25) (hlo 34)
      (by simpa [z180K18M12NineFiberMass, hv7] using hmass (7 : ZMod 9))
      (hpartition 7) (hpartition 16) (hpartition 25) (hpartition 34)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv7] using
        heq d d' (7 : ZMod 9)) c
  · exact five_equal_four_balance_zero
      (fun d => level d 8) (fun d => level d 17)
      (fun d => level d 26) (fun d => level d 35)
      (b 8) (b 17) (b 26) (b 35)
      (hlo 8) (hlo 17) (hlo 26) (hlo 35)
      (by simpa [z180K18M12NineFiberMass, hv8] using hmass (8 : ZMod 9))
      (hpartition 8) (hpartition 17) (hpartition 26) (hpartition 35)
      (by intro d d'; simpa [z180K18M12SignedNineFiber, hv8] using
        heq d d' (8 : ZMod 9)) c

/-- High-order factors plus the projection spelling of mass two force zero
signed profile on every fifth level. -/
theorem z180_k18_m12_level_signed_profiles_zero_of_high_order
    {A : Finset (ZMod 180)}
    (h10 : Polynomial.cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : Polynomial.cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : Polynomial.cyclotomic 90 Int ∣ maskPolynomial 180 A)
    (hmass : Z180K18M12ProjectionNineFibresHaveMassTwo A) :
    Z180K18M12LevelSignedProfilesZero A := by
  exact z180_k18_m12_level_signed_profiles_zero_of_eq_and_mass_two
    (z180K12ProjectionIndicator A) (z180K18M12LevelIndicator A)
    (z180K12ProjectionIndicator_nonneg A) hmass
    (sum_z180K18M12LevelIndicator A)
    (z180_k18_m12_level_signed_profiles_eq A h10 h30 h90)

/-- The exact residual finite-set interface.  Neither field contains a
Fourier, cyclotomic, spectrum, or table hypothesis. -/
structure Z180K18M12PairGeometryCombinatorialInterface where
  projection_mass_two :
    ∀ (A : Finset (ZMod 180)),
      Z180K18M12NineFibresHaveCardTwo A →
      Z180K18M12ProjectionNineFibresHaveMassTwo A
  geometry_of_signed_profiles_zero :
    ∀ (A : Finset (ZMod 180)),
      Set.InjOn z180K18Projection36 (A : Set (ZMod 180)) →
      Z180K18M12NineFibresHaveCardTwo A →
      Z180K18M12LevelSignedProfilesZero A →
      Z180K18M12PairGeometry A

/-- Assembly of the original high-order geometry field from the reduced
finite-set interface. -/
theorem z180_k18_m12_pairGeometry_of_high_order_of_combinatorial_interface
    (hcomb : Z180K18M12PairGeometryCombinatorialInterface)
    (A : Finset (ZMod 180))
    (hinj : Set.InjOn z180K18Projection36 (A : Set (ZMod 180)))
    (h10 : Polynomial.cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : Polynomial.cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : Polynomial.cyclotomic 90 Int ∣ maskPolynomial 180 A)
    (htwo : Z180K18M12NineFibresHaveCardTwo A) :
    Z180K18M12PairGeometry A := by
  have hmass := hcomb.projection_mass_two A htwo
  have hzero := z180_k18_m12_level_signed_profiles_zero_of_high_order
    h10 h30 h90 hmass
  exact hcomb.geometry_of_signed_profiles_zero A hinj htwo hzero

#print axioms z180_k18_m12_level_signed_profiles_zero_of_eq_and_mass_two
#print axioms z180_k18_m12_level_signed_profiles_zero_of_high_order
#print axioms z180_k18_m12_pairGeometry_of_high_order_of_combinatorial_interface

end Fuglede
