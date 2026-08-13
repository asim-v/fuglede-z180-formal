import Fuglede.FrequencyOrder
import Mathlib.Tactic

/-!
# Definitions for the terminal cardinality-twelve compatibility graph

This module contains only the shared predicates and colour data.  Keeping
them separate lets the kernel-reduced graph proof import no theorem proved
with `native_decide`, while the historical native certificate remains
available in `Z180K12Graph` under the same public names.
-/

namespace Fuglede

/-- The six character orders left by the exact `k = 12` branch sieve. -/
def Z180K12AllowedDifference (d : ZMod 180) : Prop :=
  d ≠ 0 ∧
    (frequencyOrder 180 d = 2 ∨
     frequencyOrder 180 d = 4 ∨
     frequencyOrder 180 d = 9 ∨
     frequencyOrder 180 d = 10 ∨
     frequencyOrder 180 d = 30 ∨
     frequencyOrder 180 d = 36)

instance z180K12AllowedDifferenceDecidable (d : ZMod 180) :
    Decidable (Z180K12AllowedDifference d) := by
  unfold Z180K12AllowedDifference
  infer_instance

/-- Reduction of a residue modulo `180` to its fifth coordinate. -/
def z180K12Fifth (d : ZMod 180) : ZMod 5 :=
  ZMod.cast d

@[simp]
theorem z180_k12_fifth_sub (x y : ZMod 180) :
    z180K12Fifth (x - y) = z180K12Fifth x - z180K12Fifth y := by
  simp [z180K12Fifth]

/-- Six-colouring table on `ZMod 12`; its entries are elements of `Fin 6`. -/
def z180K12ColorTable : ZMod 12 → Fin 6 :=
  ![0, 3, 5, 1, 5, 1, 2, 4, 2, 4, 0, 3]

/-- Colour of a residue, depending only on its coordinate modulo `12`. -/
def z180K12Color (x : ZMod 180) : Fin 6 :=
  z180K12ColorTable (ZMod.cast x)

end Fuglede
