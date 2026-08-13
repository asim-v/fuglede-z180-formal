import Fuglede.FourierTiling

/-!
Kernel-assumption audit for the Fourier zero-cover tiling bridge.

Run with `lake env lean Fuglede/FourierTilingAudit.lean`.  The printed
assumptions should contain only Lean/Mathlib's standard foundational axioms;
in particular there must be no `sorryAx`.
-/

#print axioms Fuglede.sum_fourier_product_twist
#print axioms Fuglede.representation_card_eq_one_of_fourier_zero_cover
#print axioms Fuglede.tiles_of_fourier_zero_cover
#print axioms Fuglede.tiles_of_cyclotomic_zero_cover
