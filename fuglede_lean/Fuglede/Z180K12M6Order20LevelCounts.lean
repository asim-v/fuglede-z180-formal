import Fuglede.Z180K12M6Order20LevelMass
import Mathlib.Tactic

/-!
# Cardinalities and coordinatewise sums of the order-twenty levels
-/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180K12Order20LevelCount12_nonneg
    (A : Finset (ZMod 180)) (c : ZMod 5) (r : Fin 12) :
    0 ≤ z180K12Order20LevelCount12 A c r := by
  rw [z180K12Order20LevelCount12, projection36Count12]
  exact add_nonneg
    (add_nonneg
      (z180K12ProjectionIndicator_nonneg _ _)
      (z180K12ProjectionIndicator_nonneg _ _))
    (z180K12ProjectionIndicator_nonneg _ _)

/-- The five level indicators partition every projected coordinate. -/
theorem sum_z180K12Order20LevelIndicator
    (A : Finset (ZMod 180)) (i : Fin 36) :
    (∑ c : ZMod 5, z180K12Order20LevelIndicator A c i) =
      z180K12ProjectionIndicator A i := by
  classical
  change (∑ c : ZMod 5,
      ((z180Projection36Occupancy
        (A.filter fun x ↦ crt180FifthCoord (toCRT180 x) = c) i : Nat) : Int)) =
    ((z180Projection36Occupancy A i : Nat) : Int)
  norm_cast
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter
    (A.filter fun x ↦ z180Projection36Coordinate x = i)
      (Finset.univ : Finset (ZMod 5))
      (fun x ↦ crt180FifthCoord (toCRT180 x))
  simpa [z180Projection36Occupancy, Finset.filter_filter,
    and_left_comm, and_comm, and_assoc] using hpartition

theorem sum_z180K12Order20LevelCount12
    (A : Finset (ZMod 180)) (r : Fin 12) :
    (∑ c : ZMod 5, z180K12Order20LevelCount12 A c r) =
      projection36Count12 (z180K12ProjectionIndicator A) r := by
  simp only [z180K12Order20LevelCount12, projection36Count12,
    Finset.sum_add_distrib]
  rw [sum_z180K12Order20LevelIndicator,
    sum_z180K12Order20LevelIndicator,
    sum_z180K12Order20LevelIndicator]

/-- Coordinatewise sum of the five mod-four level profiles. -/
theorem sum_z180K12Order20LevelProfiles
    (A : Finset (ZMod 180)) :
    (∑ c : ZMod 5, z180K12Order20P0
      (z180K12Order20LevelCount12 A c)) =
        z180K12Order20P0
          (projection36Count12 (z180K12ProjectionIndicator A)) ∧
    (∑ c : ZMod 5, z180K12Order20P1
      (z180K12Order20LevelCount12 A c)) =
        z180K12Order20P1
          (projection36Count12 (z180K12ProjectionIndicator A)) ∧
    (∑ c : ZMod 5, z180K12Order20P2
      (z180K12Order20LevelCount12 A c)) =
        z180K12Order20P2
          (projection36Count12 (z180K12ProjectionIndicator A)) ∧
    (∑ c : ZMod 5, z180K12Order20P3
      (z180K12Order20LevelCount12 A c)) =
        z180K12Order20P3
          (projection36Count12 (z180K12ProjectionIndicator A)) := by
  simp only [z180K12Order20P0, z180K12Order20P1,
    z180K12Order20P2, z180K12Order20P3,
    Finset.sum_add_distrib]
  rw [sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12,
    sum_z180K12Order20LevelCount12]
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

#print axioms z180K12Order20LevelCount12_mass
#print axioms sum_z180K12Order20LevelProfiles

end Fuglede
