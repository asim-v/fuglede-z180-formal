import Fuglede.Z180K30ExceptionalRawCoreV2

/-!
# Elementary semantics of the exact five-Gram certificate

These lemmas expose the pointwise exceptional-pair facts stored in the first
Boolean component of `fiveGramStarB`.  They are deliberately independent of
the catalogue normalization and can be reused by each finite shard layer.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem fiveGramStar_exceptionalPair_v82
    (U : Fin 5 → RawSet) (V : RawSet)
    (hstar : fiveGramStarB U V = true) (i : Fin 5) :
    exceptionalPairB (U i) V = true := by
  have hall :
      (List.ofFn fun j : Fin 5 => exceptionalPairB (U j) V).all id = true :=
    by
      have h := hstar
      simp only [fiveGramStarB, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
  exact (List.all_eq_true.mp hall)
    (exceptionalPairB (U i) V) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem exceptionalPair_components_v82
    {U V : RawSet} (hpair : exceptionalPairB U V = true) :
    validSixSetB U = true ∧
      validSixSetB V = true ∧
      rankTwoProjectiveCoverB U V = true ∧
      gramTraceSquare U V = scalarCoeff 936 := by
  simp only [exceptionalPairB, Bool.and_eq_true, beq_iff_eq] at hpair
  rcases hpair with ⟨⟨⟨hU, hV⟩, hcover⟩, htrace⟩
  exact ⟨hU, hV, hcover, htrace⟩

theorem fiveGramStar_components_v82
    (U : Fin 5 → RawSet) (V : RawSet)
    (hstar : fiveGramStarB U V = true) (i : Fin 5) :
    validSixSetB (U i) = true ∧
      validSixSetB V = true ∧
      rankTwoProjectiveCoverB (U i) V = true ∧
      gramTraceSquare (U i) V = scalarCoeff 936 :=
  exceptionalPair_components_v82
    (fiveGramStar_exceptionalPair_v82 U V hstar i)

#print axioms fiveGramStar_exceptionalPair_v82
#print axioms fiveGramStar_components_v82

end Fuglede.Z180K30ExceptionalRawV2
