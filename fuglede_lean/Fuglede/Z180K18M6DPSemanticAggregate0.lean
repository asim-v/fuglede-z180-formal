import Fuglede.Z180K18M6DPSemanticBase

/-! Aggregate balance leaf for residue groups `0,3,6`. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_dp_aggregate0
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    ∃ eX0 eY0 : Int,
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX0 b) (z180K18M12DPW0 b) eX0 ∧
        Z180K18M12ThreeFiberBalance
          (z180K18M12DPY0 b) (z180K18M12DPW0 b) eY0 := by
  have hx0 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx0 b) (z180K18M12DPz0 b) e := by
    refine ⟨b 0 - 1, ?_⟩
    simpa [z180K18M12DPx0, z180K18M12DPz0] using
      (z180_k18_m12_oneFiberBalance_left
        (b 0) (b 18) (d.lo 0) (d.hi 0) (d.lo 18) (d.hi 18))
  have hy0 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy0 b) (z180K18M12DPz0 b) e := by
    refine ⟨b 0 + b 9 + b 18 - 2, ?_⟩
    simpa [z180K18M12DPy0, z180K18M12DPz0] using
      (z180_k18_m12_oneFiberBalance_complement_left
        (b 0) (b 9) (b 18) (b 27)
        (d.lo 0) (d.hi 0) (d.lo 9) (d.hi 9)
        (d.lo 18) (d.hi 18) (d.lo 27) (d.hi 27) d.mass0)
  have hx3 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx3 b) (z180K18M12DPz3 b) e := by
    refine ⟨b 3 + b 12 + b 21 - 2, ?_⟩
    simpa [z180K18M12DPx3, z180K18M12DPz3] using
      (z180_k18_m12_oneFiberBalance_complement_left
        (b 3) (b 12) (b 21) (b 30)
        (d.lo 3) (d.hi 3) (d.lo 12) (d.hi 12)
        (d.lo 21) (d.hi 21) (d.lo 30) (d.hi 30) d.mass3)
  have hy3 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy3 b) (z180K18M12DPz3 b) e := by
    refine ⟨b 21 - 1, ?_⟩
    simpa [z180K18M12DPy3, z180K18M12DPz3] using
      (z180_k18_m12_oneFiberBalance_right
        (b 3) (b 21) (d.lo 3) (d.hi 3) (d.lo 21) (d.hi 21))
  have hx6 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx6 b) (z180K18M12DPz6 b) e := by
    refine ⟨b 24 - 1, ?_⟩
    simpa [z180K18M12DPx6, z180K18M12DPz6] using
      (z180_k18_m12_oneFiberBalance_right
        (b 6) (b 24) (d.lo 6) (d.hi 6) (d.lo 24) (d.hi 24))
  have hy6 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy6 b) (z180K18M12DPz6 b) e := by
    refine ⟨-b 15, ?_⟩
    simpa [z180K18M12DPy6, z180K18M12DPz6] using
      (z180_k18_m12_oneFiberBalance_complement_right
        (b 6) (b 15) (b 24) (b 33)
        (d.lo 6) (d.hi 6) (d.lo 15) (d.hi 15)
        (d.lo 24) (d.hi 24) (d.lo 33) (d.hi 33) d.mass6)
  obtain ⟨ex0, hx0⟩ := hx0
  obtain ⟨ey0, hy0⟩ := hy0
  obtain ⟨ex3, hx3⟩ := hx3
  obtain ⟨ey3, hy3⟩ := hy3
  obtain ⟨ex6, hx6⟩ := hx6
  obtain ⟨ey6, hy6⟩ := hy6
  obtain ⟨eX0, hX0⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPx0 b) (z180K18M12DPx3 b) (z180K18M12DPx6 b)
    (z180K18M12DPz0 b) (z180K18M12DPz3 b) (z180K18M12DPz6 b)
    ex0 ex3 ex6 hx0 hx3 hx6
  obtain ⟨eY0, hY0⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPy0 b) (z180K18M12DPy3 b) (z180K18M12DPy6 b)
    (z180K18M12DPz0 b) (z180K18M12DPz3 b) (z180K18M12DPz6 b)
    ey0 ey3 ey6 hy0 hy3 hy6
  refine ⟨eX0, eY0, ?_, ?_⟩
  · simpa [z180K18M12DPX0, z180K18M12DPW0] using hX0
  · simpa [z180K18M12DPY0, z180K18M12DPW0] using hY0

#print axioms z180_k18_m6_dp_aggregate0

end Fuglede
