import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem z180NondivisorK24Side1FArithmeticCore
    {a_1_10 a_1_18 a_1_36 a_1_45 a_1_180 : Int}
    (q10 : 90 * a_1_10 = 67 * a_1_180 + 82 * a_1_36 + 15 * a_1_45 - 16704)
    (q18 : 24 * a_1_18 = -55 * a_1_180 - 70 * a_1_36 - 30 * a_1_45 + 15552)
    (n10 : 0 <= a_1_10)
    (n45 : 0 <= a_1_45)
    (p56 : 8064 <= 31 * a_1_180 + 46 * a_1_36 + 30 * a_1_45)
    (p61 : 67 * a_1_180 + 82 * a_1_36 + 30 * a_1_45 <= 16704)
    (p62 : 11 * a_1_180 + 26 * a_1_36 <= 4032)
    : False := by
  have z10 : a_1_10 = 0 := by omega
  have z45 : a_1_45 = 0 := by omega
  have lower36 : 42 <= a_1_36 := by omega
  have upper36 : a_1_36 <= 102 := by omega
  have fixed36 : a_1_36 = 55 := by omega
  omega

#print axioms z180NondivisorK24Side1FArithmeticCore
