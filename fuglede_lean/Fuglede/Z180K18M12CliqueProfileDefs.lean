import Fuglede.Z180K18M12DefectProfileAudit
import Mathlib.Tactic

/-!
# Common definitions for the sharded `k = 18`, `m = 12` clique census

This module contains only the shared graph predicates, explicit color
functions, their small range checks, and the abstract interface imported by
the final aggregator.  The eight proper-color computations live in separate
fixed-index shards.

Canonical source SHA-256:
`3b8bb2943e5dfcae8e0439ae606b98d88c42da55b70384a651571274f1ca24b9`

Canonical coloring payload SHA-256:
`4f81b50bda56102c633827455b0608e24c855b6c559982971f8e30146b13f46c`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The three envelope orders absent from the unique size-eighteen profile. -/
def z180K18M12UnwantedOrder (i : Fin 3) : Nat :=
  ![2, 15, 60] i

/-- Number of colors used after fixing an unwanted edge. -/
def z180K18M12UnwantedColorBound (i : Fin 3) : Nat :=
  ![12, 11, 12] i

/-- Pointwise common-neighbour predicate for a translated edge `{0,d}`. -/
def Z180K18M12UnwantedCommonNeighbor (d z : ZMod 180) : Prop :=
  z ≠ 0 ∧ z ≠ d ∧
    frequencyOrder 180 z ∈ z180K18M12EnvelopeOrders ∧
    frequencyOrder 180 (z - d) ∈ z180K18M12EnvelopeOrders

instance (d z : ZMod 180) :
    Decidable (Z180K18M12UnwantedCommonNeighbor d z) := by
  unfold Z180K18M12UnwantedCommonNeighbor
  infer_instance

/-- A unit multiplier taking an order-fifteen value to the canonical value
`12`.  Values outside the eight relevant cases map to zero; no shard consumes
them under an order-fifteen hypothesis. -/
def z180K18M12OrderFifteenNormalizer (d : ZMod 180) : Nat :=
  if d = 12 then 1 else
  if d = 24 then 23 else
  if d = 48 then 19 else
  if d = 84 then 13 else
  if d = 96 then 17 else
  if d = 132 then 11 else
  if d = 156 then 7 else
  if d = 168 then 29 else 0

/-- Eleven-color formula on the canonical order-fifteen common-neighbour
graph, transported by the multiplier above. -/
def z180K18M12OrderFifteenColor (d z : ZMod 180) : Nat :=
  let n := (z180K18M12OrderFifteenNormalizer d * z.val) % 180
  (n + 3 * (n / 4) + 9 * (n / 9)) % 11

/-- Uniform twelve-color formula for the order-two and order-sixty
common-neighbour graphs. -/
def z180K18M12OrderTwoSixtyColor (z : ZMod 180) : Nat :=
  z.val % 4 + 4 * ((z.val / 3) % 3)

/-- The explicit color selected for each unwanted order. -/
def z180K18M12UnwantedColor
    (i : Fin 3) (d z : ZMod 180) : Nat :=
  if i = 1 then z180K18M12OrderFifteenColor d z
  else z180K18M12OrderTwoSixtyColor z

/-- Every unwanted-edge color lies below its advertised bound. -/
theorem z180_k18_m12_unwantedColor_lt :
    ∀ i : Fin 3, ∀ d z : ZMod 180,
      z180K18M12UnwantedColor i d z < z180K18M12UnwantedColorBound i := by
  decide

/-- Every unwanted-edge color bound is smaller than sixteen. -/
theorem z180_k18_m12_unwantedColorBound_lt_sixteen :
    ∀ i : Fin 3, z180K18M12UnwantedColorBound i < 16 := by
  decide

/-- The five orders which must each be realized. -/
def z180K18M12RequiredOrder (i : Fin 5) : Nat :=
  ![3, 9, 10, 30, 90] i

/-- Color bound for the graph obtained by deleting one required order. -/
def z180K18M12MissingOrderColorBound (i : Fin 5) : Nat :=
  ![12, 16, 9, 9, 9] i

/-- Explicit proper colorings after one required order is removed. -/
def z180K18M12MissingOrderColor (i : Fin 5) (z : ZMod 180) : Nat :=
  if i = 0 then z.val % 12 else
  if i = 1 then z.val % 16 else
  if i = 2 then z.val % 9 else
  if i = 3 then z.val % 3 + 3 * ((z.val / 12) % 3) else
    (z.val / 4) % 9

/-- Every missing-order color lies below its advertised bound. -/
theorem z180_k18_m12_missingOrderColor_lt :
    ∀ i : Fin 5, ∀ z : ZMod 180,
      z180K18M12MissingOrderColor i z <
        z180K18M12MissingOrderColorBound i := by
  decide

/-- Every missing-order color bound is smaller than eighteen. -/
theorem z180_k18_m12_missingOrderColorBound_lt_eighteen :
    ∀ i : Fin 5, z180K18M12MissingOrderColorBound i < 18 := by
  decide

#print axioms z180_k18_m12_unwantedColor_lt
#print axioms z180_k18_m12_unwantedColorBound_lt_sixteen
#print axioms z180_k18_m12_missingOrderColor_lt
#print axioms z180_k18_m12_missingOrderColorBound_lt_eighteen

end Fuglede
