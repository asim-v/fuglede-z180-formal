import Fuglede.Z180K18M12DPArithmeticDefs

/-! Local balance lemmas for the sharded residual `m = 12` arithmetic DAG. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_oneFiberBalance_left
    (a c : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Z180K18M12OneFiberBalance (a - c) (a + c - 1) (a - 1) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

theorem z180_k18_m12_oneFiberBalance_right
    (a c : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Z180K18M12OneFiberBalance (c - a) (a + c - 1) (c - 1) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

theorem z180_k18_m12_oneFiberBalance_complement_left
    (a b c d : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmass : a + b + c + d = 2) :
    Z180K18M12OneFiberBalance
      (b - d) (a + c - 1) (a + b + c - 2) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

theorem z180_k18_m12_oneFiberBalance_complement_right
    (a b c d : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmass : a + b + c + d = 2) :
    Z180K18M12OneFiberBalance (d - b) (a + c - 1) (-b) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

theorem z180_k18_m12_threeFiberBalance_of_oneFiber
    (x0 x1 x2 z0 z1 z2 e0 e1 e2 : Int)
    (h0 : Z180K18M12OneFiberBalance x0 z0 e0)
    (h1 : Z180K18M12OneFiberBalance x1 z1 e1)
    (h2 : Z180K18M12OneFiberBalance x2 z2 e2) :
    ∃ e : Int, Z180K18M12ThreeFiberBalance
      (x0 + x1 + x2) (z0 - z1 + z2) e := by
  refine ⟨e0 + e1 - z1 + e2 + 1, ?_⟩
  dsimp only [Z180K18M12OneFiberBalance] at h0 h1 h2
  dsimp only [Z180K18M12ThreeFiberBalance]
  omega

#print axioms z180_k18_m12_oneFiberBalance_left
#print axioms z180_k18_m12_oneFiberBalance_right
#print axioms z180_k18_m12_oneFiberBalance_complement_left
#print axioms z180_k18_m12_oneFiberBalance_complement_right
#print axioms z180_k18_m12_threeFiberBalance_of_oneFiber

end Fuglede
