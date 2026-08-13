import Fuglede.Z180K18M12PhaseFourierReindex
import Fuglede.Z180K18M12PhaseCounts
import Mathlib.Tactic

/-!
# Fourier normalization for the `k = 18`, `m = 12` branch

`Phi_60` makes the five order-twelve level sums equal.  Reindexing by the
oriented pairs extracts the common nonzero factor `1 + zeta^3`.  A singleton
pair level then identifies every raw pair-phase sum with the singleton phase.
Multiplying normalized phases by that common shift recovers the raw sums, so
each normalized count polynomial evaluates to one at a primitive twelfth
root.  The cyclotomic evaluation criterion gives divisibility by `Phi_12`.
-/

namespace Fuglede

open Polynomial

/-- The analytic bridge previously isolated as
`Z180K18M12PhaseFourierInterface.normalized_level_phi12`. -/
theorem z180_k18_m12_normalized_level_phi12
    (A : Finset (ZMod 180)) (p : Z180K18M12PairFibres A)
    (c0 : ZMod 5) (r0 : ZMod 9)
    (hsingleton : z180K18M12PairLevelFiber p c0 = {r0})
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A) :
    ∀ c : ZMod 5,
      cyclotomic 12 Int ∣
        z180K18M12NormalizedPhasePolynomial p
          (z180K18M12PairPhase p r0) c - 1 := by
  let shift : ZMod 12 := z180K18M12PairPhase p r0
  have hlevels := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    A z180K18M12OrderTwelveBaseFrequency 12
      z180K18M12OrderTwelveBaseFrequency_fifthCoord
      z180K18M12OrderTwelveBaseFrequency_order (by simpa using h60)
  intro c
  change cyclotomic 12 Int ∣
    z180K18M12NormalizedPhasePolynomial p shift c - 1
  have hfactorEq :
      z180K18M12PairRootFactor * z180K18M12PairPhaseSum p c =
        z180K18M12PairRootFactor * z180K18M12PairPhaseSum p c0 := by
    rw [← z180K18M12_fiveLevelFourierSum_factor p c,
      ← z180K18M12_fiveLevelFourierSum_factor p c0]
    exact hlevels c c0
  have hphaseSum :
      z180K18M12PairPhaseSum p c = z180K18M12PhaseChar shift := by
    have hc0 :
        z180K18M12PairPhaseSum p c0 = z180K18M12PhaseChar shift := by
      dsimp only [shift]
      exact z180K18M12_pairPhaseSum_singleton p c0 r0 hsingleton
    apply mul_left_cancel₀ z180K18M12PairRootFactor_ne_zero
    simpa only [hc0] using hfactorEq
  have hshiftEval :
      z180K18M12PhaseChar shift *
          Polynomial.aeval z180K18M12Root
            (z180K18M12NormalizedPhasePolynomial p shift c) =
        z180K18M12PhaseChar shift * 1 := by
    calc
      z180K18M12PhaseChar shift *
          Polynomial.aeval z180K18M12Root
            (z180K18M12NormalizedPhasePolynomial p shift c) =
          z180K18M12PhaseChar shift *
            z180K18M12NormalizedPhaseSum p shift c := by
        rw [z180K18M12_aeval_normalizedPhasePolynomial]
      _ = z180K18M12PairPhaseSum p c :=
        z180K18M12_shift_mul_normalizedPhaseSum p shift c
      _ = z180K18M12PhaseChar shift := hphaseSum
      _ = z180K18M12PhaseChar shift * 1 := by ring
  have heval :
      Polynomial.aeval z180K18M12Root
          (z180K18M12NormalizedPhasePolynomial p shift c) = 1 := by
    exact mul_left_cancel₀ (z180K18M12PhaseChar_ne_zero shift) hshiftEval
  rw [cyclotomic_dvd_iff_aeval_primitive (by norm_num)
    z180K18M12Root_isPrimitive]
  rw [map_sub, map_one, heval, sub_self]

/-- Canonical inhabitant of the formerly isolated analytic interface. -/
def z180K18M12PhaseFourier : Z180K18M12PhaseFourierInterface where
  normalized_level_phi12 := z180_k18_m12_normalized_level_phi12

/-- The table-free `m = 12` defect is now contradictory with no residual
interface argument. -/
theorem z180_k18_m12_defect_impossible
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (h60 : cyclotomic 60 Int ∣ maskPolynomial 180 A)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A) :
    False :=
  z180_k18_m12_defect_impossible_of_fourier_interface
    z180K18M12PhaseFourier p h60 h12

#print axioms z180_k18_m12_normalized_level_phi12
#print axioms z180_k18_m12_defect_impossible

end Fuglede
