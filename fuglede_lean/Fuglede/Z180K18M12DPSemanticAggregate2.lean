import Fuglede.Z180K18M12DPSemanticBase

/-! Aggregate balance leaf for residue groups `2,5,8`. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_aggregate2
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b) :
    ∃ eX2 eY2 : Int,
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX2 b) (z180K18M12DPW2 b) eX2 ∧
        Z180K18M12ThreeFiberBalance
          (z180K18M12DPY2 b) (z180K18M12DPW2 b) eY2 := by
  have hx2 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx2 b) (z180K18M12DPz2 b) e := by
    refine ⟨b 20 - 1, ?_⟩
    simpa [z180K18M12DPx2, z180K18M12DPz2] using
      (z180_k18_m12_oneFiberBalance_right
        (b 2) (b 20) (d.lo 2) (d.hi 2) (d.lo 20) (d.hi 20))
  have hy2 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy2 b) (z180K18M12DPz2 b) e := by
    refine ⟨-b 11, ?_⟩
    simpa [z180K18M12DPy2, z180K18M12DPz2] using
      (z180_k18_m12_oneFiberBalance_complement_right
        (b 2) (b 11) (b 20) (b 29)
        (d.lo 2) (d.hi 2) (d.lo 11) (d.hi 11)
        (d.lo 20) (d.hi 20) (d.lo 29) (d.hi 29) d.mass2)
  have hx5 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx5 b) (z180K18M12DPz5 b) e := by
    refine ⟨-b 14, ?_⟩
    simpa [z180K18M12DPx5, z180K18M12DPz5] using
      (z180_k18_m12_oneFiberBalance_complement_right
        (b 5) (b 14) (b 23) (b 32)
        (d.lo 5) (d.hi 5) (d.lo 14) (d.hi 14)
        (d.lo 23) (d.hi 23) (d.lo 32) (d.hi 32) d.mass5)
  have hy5 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy5 b) (z180K18M12DPz5 b) e := by
    refine ⟨b 5 - 1, ?_⟩
    simpa [z180K18M12DPy5, z180K18M12DPz5] using
      (z180_k18_m12_oneFiberBalance_left
        (b 5) (b 23) (d.lo 5) (d.hi 5) (d.lo 23) (d.hi 23))
  have hx8 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPx8 b) (z180K18M12DPz8 b) e := by
    refine ⟨b 8 - 1, ?_⟩
    simpa [z180K18M12DPx8, z180K18M12DPz8] using
      (z180_k18_m12_oneFiberBalance_left
        (b 8) (b 26) (d.lo 8) (d.hi 8) (d.lo 26) (d.hi 26))
  have hy8 : ∃ e, Z180K18M12OneFiberBalance
      (z180K18M12DPy8 b) (z180K18M12DPz8 b) e := by
    refine ⟨b 8 + b 17 + b 26 - 2, ?_⟩
    simpa [z180K18M12DPy8, z180K18M12DPz8] using
      (z180_k18_m12_oneFiberBalance_complement_left
        (b 8) (b 17) (b 26) (b 35)
        (d.lo 8) (d.hi 8) (d.lo 17) (d.hi 17)
        (d.lo 26) (d.hi 26) (d.lo 35) (d.hi 35) d.mass8)
  obtain ⟨ex2, hx2⟩ := hx2
  obtain ⟨ey2, hy2⟩ := hy2
  obtain ⟨ex5, hx5⟩ := hx5
  obtain ⟨ey5, hy5⟩ := hy5
  obtain ⟨ex8, hx8⟩ := hx8
  obtain ⟨ey8, hy8⟩ := hy8
  obtain ⟨eX2, hX2⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPx2 b) (z180K18M12DPx5 b) (z180K18M12DPx8 b)
    (z180K18M12DPz2 b) (z180K18M12DPz5 b) (z180K18M12DPz8 b)
    ex2 ex5 ex8 hx2 hx5 hx8
  obtain ⟨eY2, hY2⟩ := z180_k18_m12_threeFiberBalance_of_oneFiber
    (z180K18M12DPy2 b) (z180K18M12DPy5 b) (z180K18M12DPy8 b)
    (z180K18M12DPz2 b) (z180K18M12DPz5 b) (z180K18M12DPz8 b)
    ey2 ey5 ey8 hy2 hy5 hy8
  refine ⟨eX2, eY2, ?_, ?_⟩
  · simpa [z180K18M12DPX2, z180K18M12DPW2] using hX2
  · simpa [z180K18M12DPY2, z180K18M12DPW2] using hY2

#print axioms z180_k18_m12_dp_aggregate2

end Fuglede
