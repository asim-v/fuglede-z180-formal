import Fuglede.Z180K30ExceptionalProjectiveTraceTransportV88

/-!
# Symmetry of raw set equality for valid six-point sets (V85 Fix)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem rawSetEqB_of_perm_v85Fix
    {left right : RawSet} (hperm : left.Perm right) :
    rawSetEqB left right = true := by
  apply Bool.and_eq_true.mpr
  refine ⟨?_, ?_⟩
  · exact beq_iff_eq.mpr hperm.length_eq
  · apply List.all_eq_true.mpr
    intro point hpoint
    exact decide_eq_true_eq.mpr (hperm.subset hpoint)

theorem rawSetEqB_symm_of_valid_v85Fix
    {left right : RawSet}
    (hleft : validSixSetB left = true)
    (hright : validSixSetB right = true)
    (heq : rawSetEqB left right = true) :
    rawSetEqB right left = true := by
  exact rawSetEqB_of_perm_v85Fix
    (perm_of_rawSetEqB_of_valid_v88 hleft hright heq).symm

#print axioms rawSetEqB_symm_of_valid_v85Fix

end Fuglede.Z180K30ExceptionalRawV2
