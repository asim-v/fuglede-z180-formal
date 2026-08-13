import Fuglede.Z30K5InflationBridge
import Fuglede.Z180K30ExceptionalBoundary
import Mathlib.Tactic

namespace Fuglede

example (q : ZMod 30) (u : ZMod 180) :
    z30K5ScaleSix180 q * u =
      ((((6 * (q.val : ℤ)) * (u.val : ℤ) : ℤ) : ZMod 180)) := by
  unfold z30K5ScaleSix180
  norm_num [ZMod.natCast_zmod_val]

example (q : ZMod 30) (u : ZMod 180) :
    ((((q.val : ℤ) * (u.val : ℤ) : ℤ) : ZMod 30)) =
      q * z180K30Projection30 u := by
  change ((q.val : ZMod 30) * (u.val : ZMod 30)) =
    q * (ZMod.cast u : ZMod 30)
  rw [ZMod.natCast_zmod_val, ZMod.cast_eq_val]

end Fuglede
