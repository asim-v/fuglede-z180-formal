import Fuglede.Z180K18M6DPSemanticAggregate0
import Fuglede.Z180K18M6DPSemanticAggregate1
import Fuglede.Z180K18M6DPSemanticAggregate2

/-! Proof-only aggregator for the three balance leaves. -/

namespace Fuglede

theorem z180_k18_m6_dp_aggregates
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    ∃ eX0 eY0 eX1 eY1 eX2 eY2 : Int,
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX0 b) (z180K18M12DPW0 b) eX0 ∧
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPY0 b) (z180K18M12DPW0 b) eY0 ∧
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX1 b) (z180K18M12DPW1 b) eX1 ∧
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPY1 b) (z180K18M12DPW1 b) eY1 ∧
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPX2 b) (z180K18M12DPW2 b) eX2 ∧
      Z180K18M12ThreeFiberBalance
          (z180K18M12DPY2 b) (z180K18M12DPW2 b) eY2 := by
  obtain ⟨eX0, eY0, hX0, hY0⟩ := z180_k18_m6_dp_aggregate0 b d
  obtain ⟨eX1, eY1, hX1, hY1⟩ := z180_k18_m6_dp_aggregate1 b d
  obtain ⟨eX2, eY2, hX2, hY2⟩ := z180_k18_m6_dp_aggregate2 b d
  exact ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩

#print axioms z180_k18_m6_dp_aggregates

end Fuglede
