import Fuglede.Z180K18M12PhaseCombinatorics
import Fuglede.Z180K18M12PhaseCountArithmetic

/-!
# Exact remaining Fourier interface for the `m = 12` phase normalization

The pair orientation, singleton-level extraction, coefficient algebra, and
selected-mass count are proved in adjacent modules.  The only analytic bridge
still isolated here is the following cancellation statement.

At the order-twelve base character, an oriented pair contributes
`zeta^a * (1 + zeta^3)`.  `Phi_60` makes the five level sums equal.  A
singleton pair level fixes the common value; cancellation of the nonzero
factor `1 + zeta^3` then says that every normalized pair-phase polynomial has
primitive-twelfth value one, equivalently that its difference from one is
divisible by `Phi_12`.

No inhabitant of the interface is asserted in this module.
-/

namespace Fuglede

open Polynomial

/-- Minimal analytic boundary for block B.  Notice that `not Phi_12` is not a
premise: it is used outside this interface only to produce the singleton
level. -/
structure Z180K18M12PhaseFourierInterface where
  normalized_level_phi12 :
    ∀ (A : Finset (ZMod 180)) (p : Z180K18M12PairFibres A)
      (c0 : ZMod 5) (r0 : ZMod 9),
      z180K18M12PairLevelFiber p c0 = {r0} →
      cyclotomic 60 Int ∣ maskPolynomial 180 A →
      ∀ c : ZMod 5,
        cyclotomic 12 Int ∣
          z180K18M12NormalizedPhasePolynomial p
            (z180K18M12PairPhase p r0) c - 1

end Fuglede
