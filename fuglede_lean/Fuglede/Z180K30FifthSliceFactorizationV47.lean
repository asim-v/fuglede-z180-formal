import Fuglede.Z180K30FifthCoordinateErasureV45
import Fuglede.Z180K30OriginalFourierBlockGramV34
import Mathlib.Tactic

namespace Fuglede

open scoped BigOperators

noncomputable section

theorem z180K30FifthSliceFourierSumV34_eq_phase_mul_fiveLevelV47
    (X : Finset (ZMod 180)) (r : Fin 5) (d : ZMod 180) :
    z180K30FifthSliceFourierSumV34 X r d =
      ZMod.stdAddChar
          (crt180FifthCoord (toCRT180 d) * (r.val : ZMod 5)) *
        z180FiveLevelFourierSum X
          (z180K30EraseFifthCoordinateV45 d) (r.val : ZMod 5) := by
  classical
  let c : ZMod 5 := crt180FifthCoord (toCRT180 d)
  let u : CRT180 := z180K30EraseFifthCoordinateV45 d
  have hd : toCRT180 d = u + crt180FifthSingle c := by
    exact (z180K30EraseFifthCoordinateV45_add_fifthSingle d).symm
  change
    z180K30FifthSliceFourierSumV34 X r d =
      ZMod.stdAddChar (c * (r.val : ZMod 5)) *
        z180FiveLevelFourierSum X u (r.val : ZMod 5)
  unfold z180K30FifthSliceFourierSumV34
  rw [z180FiveLevelFourierSum, Finset.mul_sum]
  simp only [z180K30FifthSlice, crt180FifthCoord_toCRT180]
  apply Finset.sum_congr rfl
  intro x hx
  have hxrCast : (ZMod.cast x : ZMod 5) = (r.val : ZMod 5) :=
    (Finset.mem_filter.mp hx).2
  have hxr :
      crt180FifthCoord (toCRT180 x) = (r.val : ZMod 5) :=
    (crt180FifthCoord_toCRT180 x).trans hxrCast
  calc
    ZMod.stdAddChar (x * d) =
        z180StandardCRTCharacterPairing (toCRT180 x) (toCRT180 d) := by
      simp [z180StandardCRTCharacterPairing, fromCRT180_mul, mul_comm]
    _ = z180StandardCRTCharacterPairing
        (toCRT180 x) (u + crt180FifthSingle c) := by
      rw [hd]
    _ = z180StandardCRTCharacterPairing (toCRT180 x) u *
        ZMod.stdAddChar
          (c * crt180FifthCoord (toCRT180 x)) :=
      z180StandardCRTCharacterPairing_add_piSingle_two
        (toCRT180 x) u c
    _ = ZMod.stdAddChar (c * (r.val : ZMod 5)) *
        z180StandardCRTCharacterPairing (toCRT180 x) u := by
      rw [hxr]
      exact mul_comm _ _

#print axioms z180K30FifthSliceFourierSumV34_eq_phase_mul_fiveLevelV47

end
end Fuglede
