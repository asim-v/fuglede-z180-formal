import Fuglede.Z30K5InflationBridge
import Fuglede.Z180K30ExceptionalBoundary
import Mathlib.Tactic

namespace Fuglede

example (q : ZMod 30) (u : ZMod 180) :
    ((((q.val : ℤ) * (u.val : ℤ) : ℤ) : ZMod 30)) =
      q * z180K30Projection30 u := by
  rw [show z180K30Projection30 u = (ZMod.cast u : ZMod 30) by rfl]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.cast_eq_val]

end Fuglede
