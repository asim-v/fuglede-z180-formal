import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem z180NondivisorK24Side1EArithmeticCore
    {A B C y u : Int}
    (hA : 0 <= A)
    (hB : 0 <= B)
    (hC : 0 <= C)
    (hrel : 19 * A + 20 * B + 21 * C = 3218)
    (hy : 147 * y = 8 * A - 17 * B + 8672)
    (hu : 1764 * u = 128958 - 165 * A + 40 * B)
    : False := by
  omega

#print axioms z180NondivisorK24Side1EArithmeticCore
