import Fuglede.Z180K12M6Order20LevelDefs
import Mathlib.Tactic

/-!
# Mass of an order-twenty fifth-coordinate level

This small module isolates the only 36-coordinate normalization needed by
the level-cardinality adapter.
-/

namespace Fuglede

set_option maxHeartbeats 0

private theorem order20Mass_projection36Count12
    (b : Fin 36 → Int) :
    z180K12Order20Mass (projection36Count12 b) = ∑ i : Fin 36, b i := by
  let bn : Nat → Int := fun n ↦
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [bn, Nat.mod_eq_of_lt i.isLt]
  have hsum :
      (∑ i : Fin 36, b i) = ∑ i : Fin 36, bn i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ bn n) 36]
  norm_num [Finset.sum_range_succ, bn, z180K12Order20Mass,
    projection36Count12]
  ring

theorem z180K12Order20LevelCount12_mass
    (A : Finset (ZMod 180)) (c : ZMod 5) :
    z180K12Order20Mass (z180K12Order20LevelCount12 A c) =
      (z180FifthFiberCard A c : Int) := by
  rw [z180K12Order20LevelCount12,
    order20Mass_projection36Count12]
  change (∑ i : Fin 36,
      z180K12ProjectionIndicator
        (A.filter fun x ↦ crt180FifthCoord (toCRT180 x) = c) i) =
    (((A.filter fun x ↦
      crt180FifthCoord (toCRT180 x) = c).card : Nat) : Int)
  exact sum_z180K12ProjectionIndicator _

#print axioms z180K12Order20LevelCount12_mass

end Fuglede
