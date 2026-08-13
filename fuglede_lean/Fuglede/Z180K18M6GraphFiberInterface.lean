import Fuglede.Z180K18M6GraphLocalKernels

/-!
# Honest fibre interface for the cardinality-eighteen `m = 6` graph

The finite CRT leaves are proved in the preceding modules.  What remains is
the routine but nontrivial Finset bookkeeping described by the two fibre
bounds below.  This file names that exact boundary without asserting that it
has already been discharged.
-/

namespace Fuglede

def z180K18M6Fibre (L : Finset (ZMod 180)) (c : ZMod 5) :
    Finset (ZMod 180) :=
  L.filter fun x => z180K18M6Fifth x = c

def Z180K18M6PairwiseAllowed (L : Finset (ZMod 180)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x ≠ y → Z180K18M6AllowedDifference (x - y)

/-- Fifth-coordinate fibres containing at least two vertices. -/
def z180K18M6DoubleFibres (L : Finset (ZMod 180)) : Finset (ZMod 5) :=
  Finset.univ.filter fun c => 2 ≤ (z180K18M6Fibre L c).card

/-- The large-fibre half of the structural argument. -/
def Z180K18M6LargeFibreBound (L : Finset (ZMod 180)) : Prop :=
  ∀ c : ZMod 5, 3 ≤ (z180K18M6Fibre L c).card → L.card ≤ 9

/-- The small-fibre half.  The audited coordinate argument actually gives
the stronger bound seven because at most two fifth-coordinate fibres can
have size two. -/
def Z180K18M6SmallFibresBound (L : Finset (ZMod 180)) : Prop :=
  (∀ c : ZMod 5, (z180K18M6Fibre L c).card ≤ 2) → L.card ≤ 7

/-- Geometric content needed in the all-small-fibres case: no three
fifth-coordinate fibres can all contain compatible pairs. -/
def Z180K18M6DoubleFibreBound (L : Finset (ZMod 180)) : Prop :=
  (z180K18M6DoubleFibres L).card ≤ 2

end Fuglede
