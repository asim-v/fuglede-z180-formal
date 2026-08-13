import Fuglede.Z180K30ExceptionalProjectiveTraceTransportV88

/-!
# Symmetry of raw set equality for valid six-point sets (V85 Fix2)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem rawSetEqB_of_perm_v85Fix2
    {left right : RawSet} (hperm : left.Perm right) :
    rawSetEqB left right = true := by
  simp only [rawSetEqB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨hperm.length_eq, ?_⟩
  apply List.all_eq_true.mpr
  intro point hpoint
  exact decide_eq_true_eq.mpr (hperm.subset hpoint)

theorem rawSetEqB_symm_of_valid_v85Fix2
    {left right : RawSet}
    (hleft : validSixSetB left = true)
    (hright : validSixSetB right = true)
    (heq : rawSetEqB left right = true) :
    rawSetEqB right left = true := by
  exact rawSetEqB_of_perm_v85Fix2
    (perm_of_rawSetEqB_of_valid_v88 hleft hright heq).symm

#print axioms rawSetEqB_symm_of_valid_v85Fix2

end Fuglede.Z180K30ExceptionalRawV2
