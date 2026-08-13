import Fuglede.FrequencyOrder
import Fuglede.CRT180
import Mathlib.Tactic

/-!
# Core definitions for the K18 `m = 6` compatibility graph

The 180-by-180 CRT truth table is deliberately absent from this module and
lives in eighteen generated opaque shards.  The coordinate injectivity proof
is algebraic through the existing CRT equivalence.
-/

namespace Fuglede

def Z180K18M6AllowedDifference (d : ZMod 180) : Prop :=
  d ≠ 0 ∧
    (frequencyOrder 180 d = 3 ∨
     frequencyOrder 180 d = 4 ∨
     frequencyOrder 180 d = 9 ∨
     frequencyOrder 180 d = 15 ∨
     frequencyOrder 180 d = 20 ∨
     frequencyOrder 180 d = 30 ∨
     frequencyOrder 180 d = 180)

instance z180K18M6AllowedDifferenceDecidable (d : ZMod 180) :
    Decidable (Z180K18M6AllowedDifference d) := by
  unfold Z180K18M6AllowedDifference
  infer_instance

abbrev Z180K18M6BaseCoord := ZMod 4 × ZMod 9

def z180K18M6BaseCoord (x : ZMod 180) : Z180K18M6BaseCoord :=
  ((ZMod.cast x : ZMod 4), (ZMod.cast x : ZMod 9))

def z180K18M6Fifth (x : ZMod 180) : ZMod 5 :=
  ZMod.cast x

def z180K18M6Parity (x : Z180K18M6BaseCoord) : ZMod 2 :=
  ZMod.cast x.1

def z180K18M6Third (x : Z180K18M6BaseCoord) : ZMod 3 :=
  ZMod.cast x.2

def Z180K18M6SameLevelCompatible
    (x y : Z180K18M6BaseCoord) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = y.2 ∧ z180K18M6Parity x ≠ z180K18M6Parity y)

instance z180K18M6SameLevelCompatibleDecidable
    (x y : Z180K18M6BaseCoord) :
    Decidable (Z180K18M6SameLevelCompatible x y) := by
  unfold Z180K18M6SameLevelCompatible
  infer_instance

def Z180K18M6CrossLevelCompatible
    (x y : Z180K18M6BaseCoord) : Prop :=
  (z180K18M6Parity x = z180K18M6Parity y ∧
      z180K18M6Third x = z180K18M6Third y ∧ x.2 ≠ y.2) ∨
    (z180K18M6Parity x ≠ z180K18M6Parity y ∧
      (x.2 = y.2 ∨ z180K18M6Third x ≠ z180K18M6Third y))

instance z180K18M6CrossLevelCompatibleDecidable
    (x y : Z180K18M6BaseCoord) :
    Decidable (Z180K18M6CrossLevelCompatible x y) := by
  unfold Z180K18M6CrossLevelCompatible
  infer_instance

theorem z180_k18_m6_crt_coordinates_injective :
    Function.Injective
      (fun x : ZMod 180 => (z180K18M6BaseCoord x, z180K18M6Fifth x)) := by
  intro x y hxy
  have hbase : z180K18M6BaseCoord x = z180K18M6BaseCoord y :=
    congrArg Prod.fst hxy
  have h4 : (ZMod.cast x : ZMod 4) = ZMod.cast y :=
    congrArg Prod.fst hbase
  have h9 : (ZMod.cast x : ZMod 9) = ZMod.cast y :=
    congrArg Prod.snd hbase
  have h5 : (ZMod.cast x : ZMod 5) = ZMod.cast y :=
    congrArg Prod.snd hxy
  apply toCRT180_injective
  funext i
  rw [toCRT180_apply, toCRT180_apply]
  fin_cases i
  · change (ZMod.cast x : ZMod 4) = ZMod.cast y
    exact h4
  · change (ZMod.cast x : ZMod 9) = ZMod.cast y
    exact h9
  · change (ZMod.cast x : ZMod 5) = ZMod.cast y
    exact h5

#print axioms z180_k18_m6_crt_coordinates_injective

end Fuglede
