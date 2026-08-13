import Fuglede.Z180FiveLevelFourier
import Mathlib.Tactic

namespace Fuglede

noncomputable section

noncomputable def z180K30EraseFifthCoordinateV45 (d : ZMod 180) : CRT180 :=
  toCRT180 d - crt180FifthSingle (crt180FifthCoord (toCRT180 d))

@[simp]
theorem z180K30EraseFifthCoordinateV45_fifthCoord (d : ZMod 180) :
    crt180FifthCoord (z180K30EraseFifthCoordinateV45 d) = 0 := by
  rw [z180K30EraseFifthCoordinateV45]
  change (toCRT180 d) 2 -
    (crt180FifthSingle (crt180FifthCoord (toCRT180 d))) 2 = 0
  rw [crt180FifthSingle_apply_two]
  exact sub_self _

theorem z180K30EraseFifthCoordinateV45_add_fifthSingle (d : ZMod 180) :
    z180K30EraseFifthCoordinateV45 d +
      crt180FifthSingle (crt180FifthCoord (toCRT180 d)) = toCRT180 d := by
  rw [z180K30EraseFifthCoordinateV45]
  exact sub_add_cancel _ _

@[simp]
theorem fromCRT180_eraseFifthCoordinateV45_add_fifthSingle (d : ZMod 180) :
    fromCRT180 (z180K30EraseFifthCoordinateV45 d +
      crt180FifthSingle (crt180FifthCoord (toCRT180 d))) = d := by
  rw [z180K30EraseFifthCoordinateV45_add_fifthSingle, fromCRT180_toCRT180]

theorem z180FiveLevelFourierSum_eq_of_cyclotomicZero_eraseV45
    (X : Finset (ZMod 180)) (d : ZMod 180)
    (hfifth : crt180FifthCoord (toCRT180 d) ≠ 0)
    (hzero : CyclotomicZero 180 X d) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X (z180K30EraseFifthCoordinateV45 d) c =
      z180FiveLevelFourierSum X (z180K30EraseFifthCoordinateV45 d) c' := by
  apply z180FiveLevelFourierSum_eq_of_cyclotomic_mul_five
    X (z180K30EraseFifthCoordinateV45 d)
    (z180K30EraseFifthCoordinateV45_fifthCoord d)
  unfold CyclotomicZero at hzero
  have hord := frequencyOrder_fromCRT180_add_fifth
    (z180K30EraseFifthCoordinateV45 d)
    (z180K30EraseFifthCoordinateV45_fifthCoord d) hfifth
  rw [← hord]
  simpa only [fromCRT180_eraseFifthCoordinateV45_add_fifthSingle] using hzero

#print axioms z180FiveLevelFourierSum_eq_of_cyclotomicZero_eraseV45

end
end Fuglede
