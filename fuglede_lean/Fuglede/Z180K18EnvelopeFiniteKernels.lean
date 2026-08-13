import Mathlib.Tactic

/-!
# Small arithmetic kernels for the (k = 18) envelope audit

These theorems contain no set-level or Fourier assumptions.  They are the
kernel-checkable arithmetic endpoints of two external finite reductions.

The first replaces the 343-state `(Phi_2,Phi_6)` packed DP by three bounded
integers.  In the canonical audit, the three residue classes modulo three
contribute respectively

`2(a,a,0)`, `2(b,0,-b)`, and `2(c,-c,c)`,

where each of `a,b,c` is a sum of three values in `{-1,0,1}`.  Hence all
three lie in `[-3,3]`.  Coordinatewise divisibility by five forces them all
to vanish, contradicting the nonzero `Phi_2` defect remainder.

The second is the common endpoint of the three level-size exclusions:
five positive multiples of three, all congruent modulo two, cannot sum to
eighteen.
-/

namespace Fuglede

/-- Algebraic replacement for the canonical 343-state `(2,6)` packed DP. -/
theorem z180_k18_m2_phi2_phi6_pairRemainder_kernel
    (a b c k2 k60 k61 : Int)
    (haLo : -3 ≤ a) (haHi : a ≤ 3)
    (hbLo : -3 ≤ b) (hbHi : b ≤ 3)
    (hcLo : -3 ≤ c) (hcHi : c ≤ 3)
    (h2 : 2 * (a + b + c) = 5 * k2)
    (h60 : 2 * (a - c) = 5 * k60)
    (h61 : 2 * (-b + c) = 5 * k61)
    (h2ne : 2 * (a + b + c) ≠ 0) :
    False := by
  omega

/-- Common Presburger endpoint of the `q=15,45` level-size audits. -/
theorem z180_k18_five_level_sizes_impossible
    (s0 s1 s2 s3 s4 : Int)
    (t0 t1 t2 t3 t4 : Int)
    (e1 e2 e3 e4 : Int)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hs3 : 0 < s3) (hs4 : 0 < s4)
    (ht0 : s0 = 3 * t0) (ht1 : s1 = 3 * t1)
    (ht2 : s2 = 3 * t2) (ht3 : s3 = 3 * t3)
    (ht4 : s4 = 3 * t4)
    (he1 : s1 - s0 = 2 * e1) (he2 : s2 - s0 = 2 * e2)
    (he3 : s3 - s0 = 2 * e3) (he4 : s4 - s0 = 2 * e4)
    (hsum : s0 + s1 + s2 + s3 + s4 = 18) :
    False := by
  omega

#print axioms z180_k18_m2_phi2_phi6_pairRemainder_kernel
#print axioms z180_k18_five_level_sizes_impossible

end Fuglede
