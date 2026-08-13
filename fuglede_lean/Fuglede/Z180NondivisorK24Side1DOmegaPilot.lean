import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Isolated six-formula Presburger pilot for k=24 outer leaf 621. -/

theorem z180NondivisorK24Side1DOmegaPilot
    {a_1_6 a_1_15 a_1_18 a_1_30 a_1_36 a_1_45 a_1_60 a_1_90 a_1_180 : Int}
    (p0 : 0 <= 1152 - 6 * a_1_36 - 6 * a_1_180)
    (p1 : 0 <= -4176 + 15 * a_1_15 - 28 * a_1_18 + 15 * a_1_30
      + 38 * a_1_36 - 15 * a_1_60 - 28 * a_1_90 + 38 * a_1_180)
    (p2 : 0 <= -8640 - 45 * a_1_15 - 45 * a_1_30 + 40 * a_1_36
      - 70 * a_1_45 + 45 * a_1_60 - 70 * a_1_90 + 110 * a_1_180)
    (p3 : 0 <= -8352 + 30 * a_1_15 + 28 * a_1_18 + 30 * a_1_30
      + 34 * a_1_36 - 30 * a_1_60 + 28 * a_1_90 + 34 * a_1_180)
    (p4 : 0 <= -8640 - 45 * a_1_15 - 45 * a_1_30 + 40 * a_1_36
      + 35 * a_1_45 + 45 * a_1_60 + 35 * a_1_90 + 5 * a_1_180)
    (q6 : 28 * a_1_6 = 4752 - 5 * a_1_15 - 33 * a_1_30
      - 22 * a_1_36 + 5 * a_1_60 - 22 * a_1_180)
    : False := by
  have cutX :
      3 * a_1_6 + 2 * a_1_180 - 3 * a_1_36 + 7 * a_1_15
        + 10 * a_1_30 - 7 * a_1_60 - 5 * a_1_90 - 5 * a_1_45 <= -658 := by
    omega
  omega

#print axioms z180NondivisorK24Side1DOmegaPilot
