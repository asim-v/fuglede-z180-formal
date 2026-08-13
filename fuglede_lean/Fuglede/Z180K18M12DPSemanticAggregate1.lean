import Fuglede.Z180K18M12DPSemanticBase

/-! Aggregate balance leaf for residue groups `1,4,7`. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_aggregate1
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b) :
    ∃ eX1 eY1 : Int,
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX1 b) (z180K18M12DPW1 b) eX1 ∧
        Z180K18M12ThreeFiberBalance
          (z180K18M12DPY1 b) (z180K18M12DPW1 b) eY1 := by
  have hx1 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx1 b) (z180K18M12DPz1 b) e := by
    refine ⟨-b 10, ?_⟩
    simpa [z180K18M12DPx1, z180K18M12DPz1] using
      (z180_k18_m12_oneFiberBalance_complement_right
        (b 1) (b 10) (b 19) (b 28)
        (d.lo 1) (d.hi 1) (d.lo 10) (d.hi 10)
        (d.lo 19) (d.hi 19) (d.lo 28) (d.hi 28) d.mass1)
  have hy1 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy1 b) (z180K18M12DPz1 b) e := by
    refine ⟨b 1 - 1, ?_⟩
    simpa [z180K18M12DPy1, z180K18M12DPz1] using
      (z180_k18_m12_oneFiberBalance_left
        (b 1) (b 19) (d.lo 1) (d.hi 1) (d.lo 19) (d.hi 19))
  have hx4 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx4 b) (z180K18M12DPz4 b) e := by
    refine ⟨b 4 - 1, ?_⟩
    simpa [z180K18M12DPx4, z180K18M12DPz4] using
      (z180_k18_m12_oneFiberBalance_left
        (b 4) (b 22) (d.lo 4) (d.hi 4) (d.lo 22) (d.hi 22))
  have hy4 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy4 b) (z180K18M12DPz4 b) e := by
    refine ⟨b 4 + b 13 + b 22 - 2, ?_⟩
    simpa [z180K18M12DPy4, z180K18M12DPz4] using
      (z180_k18_m12_oneFiberBalance_complement_left
        (b 4) (b 13) (b 22) (b 31)
        (d.lo 4) (d.hi 4) (d.lo 13) (d.hi 13)
        (d.lo 22) (d.hi 22) (d.lo 31) (d.hi 31) d.mass4)
  have hx7 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx7 b) (z180K18M12DPz7 b) e := by
    refine ⟨b 7 + b 16 + b 25 - 2, ?_⟩
    simpa [z180K18M12DPx7, z180K18M12DPz7] using
      (z180_k18_m12_oneFiberBalance_complement_left
        (b 7) (b 16) (b 25) (b 34)
        (d.lo 7) (d.hi 7) (d.lo 16) (d.hi 16)
        (d.lo 25) (d.hi 25) (d.lo 34) (d.hi 34) d.mass7)
  have hy7 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy7 b) (z180K18M12DPz7 b) e := by
    refine ⟨b 25 - 1, ?_⟩
    simpa [z180K18M12DPy7, z180K18M12DPz7] using
      (z180_k18_m12_oneFiberBalance_right
        (b 7) (b 25) (d.lo 7) (d.hi 7) (d.lo 25) (d.hi 25))
  obtain ⟨ex1, hx1⟩ := hx1
  obtain ⟨ey1, hy1⟩ := hy1
  obtain ⟨ex4, hx4⟩ := hx4
  obtain ⟨ey4, hy4⟩ := hy4
  obtain ⟨ex7, hx7⟩ := hx7
  obtain ⟨ey7, hy7⟩ := hy7
  obtain ⟨eX1, hX1⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPx1 b) (z180K18M12DPx4 b) (z180K18M12DPx7 b)
    (z180K18M12DPz1 b) (z180K18M12DPz4 b) (z180K18M12DPz7 b)
    ex1 ex4 ex7 hx1 hx4 hx7
  obtain ⟨eY1, hY1⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPy1 b) (z180K18M12DPy4 b) (z180K18M12DPy7 b)
    (z180K18M12DPz1 b) (z180K18M12DPz4 b) (z180K18M12DPz7 b)
    ey1 ey4 ey7 hy1 hy4 hy7
  refine ⟨eX1, eY1, ?_, ?_⟩
  · simpa [z180K18M12DPX1, z180K18M12DPW1] using hX1
  · simpa [z180K18M12DPY1, z180K18M12DPW1] using hY1

#print axioms z180_k18_m12_dp_aggregate1

end Fuglede
