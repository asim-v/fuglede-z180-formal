import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Explicit affine witnesses for literal K30 exceptional pairs

The Boolean checked by each generated leaf contains no affine-orbit search.
It checks the exceptional-pair arithmetic and one supplied affine equality
for each marginal.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def literalOrbitRepresentativeV87 (o : Fin 8) : RawSet :=
  match o.val with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [0, 10, 12, 18, 24, 30]
  | 2 => [0, 10, 12, 22, 24, 34]
  | 3 => [0, 12, 15, 18, 24, 30]
  | 4 => [0, 12, 15, 18, 30, 33]
  | 5 => [0, 12, 16, 18, 24, 30]
  | 6 => [0, 12, 18, 21, 24, 30]
  | _ => [0, 6, 12, 18, 24, 30]

structure LiteralExceptionalPairWitnessV87 where
  U : RawSet
  V : RawSet
  uRepresentative : Fin 8
  uUnit : RawPoint
  uTranslation : RawPoint
  vRepresentative : Fin 8
  vUnit : RawPoint
  vTranslation : RawPoint

def literalAffineWitnessB_v87
    (set : RawSet) (representative : Fin 8)
    (unit translation : RawPoint) : Bool :=
  decide (unit ∈ units36) &&
    rawSetEqB
      (affineSet unit translation
        (literalOrbitRepresentativeV87 representative)) set

def literalExceptionalPairWitnessB_v87
    (w : LiteralExceptionalPairWitnessV87) : Bool :=
  exceptionalPairB w.U w.V &&
    (literalAffineWitnessB_v87 w.U w.uRepresentative
        w.uUnit w.uTranslation &&
      literalAffineWitnessB_v87 w.V w.vRepresentative
        w.vUnit w.vTranslation)

structure CertifiedLiteralExceptionalWitnessShardV87 where
  divisor : Nat
  supported_divisor :
    divisor = 3 ∨ divisor = 4 ∨ divisor = 6
  witnesses : List LiteralExceptionalPairWitnessV87
  verified : witnesses.all literalExceptionalPairWitnessB_v87 = true

theorem literalOrbitRepresentativeV87_mem
    (o : Fin 8) : literalOrbitRepresentativeV87 o ∈ orbitRepresentatives := by
  fin_cases o <;> decide

theorem orbitCoveredB_of_literalAffineWitnessB_v87
    (set : RawSet) (representative : Fin 8)
    (unit translation : RawPoint)
    (hwitness : literalAffineWitnessB_v87 set representative
      unit translation = true) :
    orbitCoveredB set = true := by
  simp only [literalAffineWitnessB_v87, Bool.and_eq_true] at hwitness
  rw [orbitCoveredB]
  apply List.any_eq_true.mpr
  refine ⟨literalOrbitRepresentativeV87 representative,
    literalOrbitRepresentativeV87_mem representative, ?_⟩
  rw [affineEquivalentB]
  apply List.any_eq_true.mpr
  refine ⟨unit, of_decide_eq_true hwitness.1, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨translation, by simp [rawUniverse], hwitness.2⟩

theorem literalExceptionalPairWitnessB_v87_semantics
    (w : LiteralExceptionalPairWitnessV87)
    (hverified : literalExceptionalPairWitnessB_v87 w = true) :
    exceptionalPairB w.U w.V = true ∧
      orbitCoveredB w.U = true ∧ orbitCoveredB w.V = true := by
  simp only [literalExceptionalPairWitnessB_v87,
    Bool.and_eq_true] at hverified
  exact ⟨hverified.1,
    orbitCoveredB_of_literalAffineWitnessB_v87
      w.U w.uRepresentative w.uUnit w.uTranslation hverified.2.1,
    orbitCoveredB_of_literalAffineWitnessB_v87
      w.V w.vRepresentative w.vUnit w.vTranslation hverified.2.2⟩

#print axioms literalExceptionalPairWitnessB_v87_semantics

end Fuglede.Z180K30ExceptionalRawV2
