import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem z180NondivisorK24Side0BArithmeticCore
    {a_0_12 a_0_15 a_0_18 a_0_20 a_0_30 a_0_36 a_0_45 a_0_60 a_0_90 : Int}
    (q12 : 24 * a_0_12 = 12 * a_0_30 + 16 * a_0_36 - 5 * a_0_45 + 6 * a_0_60 - 5 * a_0_90 - 768)
    (q18 : 16 * a_0_18 = -24 * a_0_30 - 56 * a_0_36 - 25 * a_0_45 - 21 * a_0_90 + 9984)
    (n12 : 0 <= a_0_12)
    (n15 : 0 <= a_0_15)
    (n18 : 0 <= a_0_18)
    (n20 : 0 <= a_0_20)
    (n30 : 0 <= a_0_30)
    (n36 : 0 <= a_0_36)
    (n45 : 0 <= a_0_45)
    (n60 : 0 <= a_0_60)
    (n90 : 0 <= a_0_90)
    (p60 : 0 < a_0_60)
    (i21 : 20736 <= 40 * a_0_15 + 20 * a_0_20 + 72 * a_0_30 + 144 * a_0_36 + 55 * a_0_45 + 20 * a_0_60 + 15 * a_0_90)
    (i24 : 20 * a_0_20 - 24 * a_0_36 - 15 * a_0_45 + 20 * a_0_60 - 15 * a_0_90 + 4608 <= 0)
    (i27 : 0 <= 2 * a_0_15 + a_0_20 - a_0_45 + a_0_60)
    (i29 : 3 * a_0_15 + 4 * a_0_20 + 3 * a_0_30 - a_0_45 + a_0_60 - a_0_90 <= 0)
    (i32 : 0 <= a_0_15 + 2 * a_0_20 + 3 * a_0_30 - a_0_45 + 2 * a_0_60 - a_0_90)
    : False := by
  have z15 : a_0_15 = 0 := by omega
  have z18 : a_0_18 = 0 := by omega
  have z20 : a_0_20 = 0 := by omega
  have one60 : a_0_60 = 1 := by omega
  have lower30 : 45 <= a_0_30 := by omega
  have upper30 : a_0_30 <= 46 := by omega
  have lower36 : 106 <= a_0_36 := by omega
  have upper36 : a_0_36 <= 108 := by omega
  have upper45 : a_0_45 <= 1 := by omega
  have lower90 : 136 <= a_0_90 := by omega
  have upper90 : a_0_90 <= 139 := by omega
  omega

#print axioms z180NondivisorK24Side0BArithmeticCore
