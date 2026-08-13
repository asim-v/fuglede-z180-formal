import Mathlib.Tactic

namespace Fuglede

/- A context-free integer split used by generated DPLL certificates. Keeping
   `omega` here prevents it from reprocessing the large arithmetic context at
   every internal cut node. -/
theorem z180IntSuccSplit (x lower : Int) :
    x ≤ lower ∨ lower + 1 ≤ x := by
  omega

#print axioms z180IntSuccSplit

end Fuglede
