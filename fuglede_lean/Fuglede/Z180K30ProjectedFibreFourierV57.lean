import Fuglede.Z180K30NormalGramOperatorV56
import Fuglede.Z180K30FibreFourier
import Fuglede.Z180K30CommonSpectrumInterface
import Mathlib.Tactic

namespace Fuglede

noncomputable section

noncomputable def z180K30ProjectedFibreEnumV57
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Fin 6 → ZMod 36 :=
  fun k => z180K30Projection36
    (z180K30OriginalFibreEnumV32 X i hcard k)

theorem z180K30ProjectedFibreEnumV57_mem
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30ProjectedFibreEnumV57 X i hcard k ∈
      z180K30FifthFibres36 X i := by
  unfold z180K30ProjectedFibreEnumV57 z180K30FifthFibres36
  rw [z180K30Fibre]
  apply Finset.mem_image.mpr
  refine ⟨z180K30OriginalFibreEnumV32 X i hcard k, ?_, rfl⟩
  exact z180K30OriginalFibreEnumV32_mem_slice X i hcard k

theorem z180K30ProjectedFibreEnumV57_injective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Function.Injective (z180K30ProjectedFibreEnumV57 X i hcard) := by
  intro j k hjk
  apply z180K30OriginalFibreEnumV32_injective X i hcard
  apply z180_k30_cast36_injective_on_fifth_fibre
  · exact z180K30OriginalFibreEnumV32_fifth X i hcard j
  · exact z180K30OriginalFibreEnumV32_fifth X i hcard k
  · exact hjk

theorem z180K30ProjectedFibreEnumV57_surjective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    ∀ y ∈ z180K30FifthFibres36 X i,
      ∃ k, z180K30ProjectedFibreEnumV57 X i hcard k = y := by
  classical
  intro y hy
  unfold z180K30FifthFibres36 z180K30Fibre at hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
  let E := Finset.equivFinOfCardEq
    (z180K30FifthSlice_card_of_projected_card_v31 X i hcard)
  obtain ⟨k, hk⟩ := E.symm.surjective
    (⟨x, hx⟩ : ↥(z180K30FifthSlice X (i.val : ZMod 5)))
  refine ⟨k, ?_⟩
  unfold z180K30ProjectedFibreEnumV57
  change z180K30Projection36 ((E.symm k).1) = y
  rw [hk]
  exact hxy

set_option maxRecDepth 100000 in
theorem z180K30LiftFrequency36_unit29_projection_v57
    (d : ZMod 180) (hfive : (ZMod.cast d : ZMod 5) = 0) :
    z180K30LiftFrequency36
        ((29 : ZMod 36) * z180K30Projection36 d) = d := by
  revert d
  decide

set_option maxRecDepth 100000 in
theorem frequencyOrder_unit29_z36_v57 (d : ZMod 36) :
    frequencyOrder 36 ((29 : ZMod 36) * d) = frequencyOrder 36 d := by
  revert d
  decide

theorem z180K30FifthSliceFourierSum_eq_twisted_projection_v57
    (X : Finset (ZMod 180)) (r : Fin 5) (d : ZMod 180)
    (hfive : (ZMod.cast d : ZMod 5) = 0) :
    z180K30FifthSliceFourierSumV34 X r d =
      fourierSum (z180K30FifthFibres36 X r)
        ((29 : ZMod 36) * z180K30Projection36 d) := by
  have hcoord : crt180FifthCoord (toCRT180 d) = 0 := by
    exact (crt180FifthCoord_toCRT180 d).trans hfive
  have herase : z180K30EraseFifthCoordinateV45 d = toCRT180 d := by
    rw [z180K30EraseFifthCoordinateV45]
    rw [hcoord]
    simp
  change z180K30FifthSliceFourierSumV34 X r d =
    fourierSum (z180K30Fibre X (r.val : ZMod 5))
      ((29 : ZMod 36) * z180K30Projection36 d)
  rw [fourierSum_z180K30FifthFiber36]
  rw [z180K30LiftFrequency36_unit29_projection_v57 d hfive]
  rw [z180K30FifthSliceFourierSumV34_eq_phase_mul_fiveLevelV47]
  rw [hcoord, herase]
  simp

theorem cyclotomicZero_of_unit29_v57
    (X : Finset (ZMod 36)) (d : ZMod 36)
    (hzero : CyclotomicZero 36 X ((29 : ZMod 36) * d)) :
    CyclotomicZero 36 X d := by
  unfold CyclotomicZero at hzero ⊢
  rw [frequencyOrder_unit29_z36_v57] at hzero
  exact hzero

#print axioms z180K30ProjectedFibreEnumV57_surjective
#print axioms z180K30FifthSliceFourierSum_eq_twisted_projection_v57
#print axioms cyclotomicZero_of_unit29_v57

end
end Fuglede
