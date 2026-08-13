import Fuglede.Z180K12M6Order15SemanticHigh
import Fuglede.Z180K12M6Order45SemanticHigh
import Fuglede.Z180K12M6Order60SemanticHigh
import Fuglede.Z180K12M6Order90SemanticHigh
import Fuglede.Z180K12M6Order180SemanticHigh

/-! # Combined exact high-order exclusions for the `k = 12` sieve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

theorem z180_k12_m6_cyclotomicZero_order_ne_high_five
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A)
    {d : ZMod 180} (hzero : CyclotomicZero 180 A d) :
    frequencyOrder 180 d ≠ 15 ∧ frequencyOrder 180 d ≠ 45 ∧
      frequencyOrder 180 d ≠ 60 ∧ frequencyOrder 180 d ≠ 90 ∧
      frequencyOrder 180 d ≠ 180 := by
  have h15 := z180_k12_m6_not_cyclotomic_fifteen_high
    hcard hinj htransform2 htransform4 hdefect
  have h45 := z180_k12_m6_not_cyclotomic_fortyfive_high
    hcard hinj htransform2 htransform4 hdefect
  have h60 := z180_k12_m6_not_cyclotomic_sixty_high
    hcard hinj htransform2 htransform4 hdefect
  have h90 := z180_k12_m6_not_cyclotomic_ninety_high
    hcard hinj htransform2 htransform4 hdefect
  have h180 := z180_k12_m6_not_cyclotomic_oneeighty_high
    hcard hinj htransform2 htransform4 hdefect
  constructor
  · intro horder
    exact h15 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h45 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h60 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h90 (by simpa [CyclotomicZero, horder] using hzero)
  · intro horder
    exact h180 (by simpa [CyclotomicZero, horder] using hzero)

#print axioms z180_k12_m6_cyclotomicZero_order_ne_high_five

end Z180K12HighOrder

end Fuglede
