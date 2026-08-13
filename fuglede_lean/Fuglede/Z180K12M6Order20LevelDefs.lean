import Fuglede.Z180FiveLevelCardinality
import Fuglede.Z180K12M6Order20Remainders
import Fuglede.Z180K12M6SemanticCommon
import Mathlib.Tactic

/-!
# Fifth-coordinate levels for the order-twenty branch
-/

namespace Fuglede

open scoped BigOperators

noncomputable def z180K12Order20FifthLevel
    (A : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 180) :=
  A.filter fun x ↦ crt180FifthCoord (toCRT180 x) = c

noncomputable def z180K12Order20LevelIndicator
    (A : Finset (ZMod 180)) (c : ZMod 5) : Fin 36 → Int :=
  z180K12ProjectionIndicator (z180K12Order20FifthLevel A c)

noncomputable def z180K12Order20LevelCount12
    (A : Finset (ZMod 180)) (c : ZMod 5) : Fin 12 → Int :=
  projection36Count12 (z180K12Order20LevelIndicator A c)

noncomputable def z180OrderFourBaseFrequency : CRT180 :=
  toCRT180 (45 : ZMod 180)

@[simp]
theorem z180OrderFourBaseFrequency_fifthCoord :
    crt180FifthCoord z180OrderFourBaseFrequency = 0 := by
  change (ZMod.cast (45 : ZMod 180) : ZMod 5) = 0
  decide

@[simp]
theorem z180OrderFourBaseFrequency_order :
    frequencyOrder 180 (fromCRT180 z180OrderFourBaseFrequency) = 4 := by
  rw [z180OrderFourBaseFrequency, fromCRT180_toCRT180]
  decide

theorem sum_zmod_five_explicit_order20
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

theorem z180K12Order20_fiveLevelFourierSum_eq_fourierSum
    (A : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) :
    z180FiveLevelFourierSum A u c =
      fourierSum (z180K12Order20FifthLevel A c) (fromCRT180 u) := by
  rw [← z180StandardCRTFourierSum_eq_fourierSum]
  rfl

#print axioms z180OrderFourBaseFrequency_order
#print axioms sum_zmod_five_explicit_order20
#print axioms z180K12Order20_fiveLevelFourierSum_eq_fourierSum

end Fuglede
