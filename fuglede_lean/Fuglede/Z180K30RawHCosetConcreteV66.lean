import Fuglede.Z180K30ExceptionalRawFibreV63Fix
import Fuglede.Z180K30ExceptionalAffineHBridgeV64Fix
import Fuglede.Z180K30CatalogueAlternativeV65
import Fuglede.Z180K30ExceptionalHCoordinateCoreV5

/-!
# From the raw H-coset certificate to a concrete K30 column

This module transports the Boolean `HCosetB` predicate on the faithful raw
fibre back to the genuine `ZMod 36` fifth fibre.  It also packages the
catalogue-to-concrete corollary obtained from the V65 and V64Fix bridges.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

set_option maxRecDepth 100000 in
private theorem z36K30_H_class_card_v66 (rho : ZMod 6) :
    ((Finset.univ : Finset (ZMod 36)).filter
      (fun q => z36K30Projection6 q = rho)).card = 6 := by
  fin_cases rho <;> decide

theorem z180_k30_HCosetColumnConcrete_of_raw_v66
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6)
    (hraw : HCosetB (z180K30RawFibreV63Fix X i hcard) = true) :
    Z180K30HCosetColumnConcrete X i := by
  classical
  unfold HCosetB at hraw
  have hparts := Bool.and_eq_true.mp hraw
  rcases List.any_eq_true.mp hparts.2 with
    ⟨residue, hresidueRange, hresidueAll⟩
  have hresidueLt : residue < 6 := List.mem_range.mp hresidueRange
  have hpointMod (point : RawPoint)
      (hpoint : point ∈ z180K30RawFibreV63Fix X i hcard) :
      point.val % 6 = residue := by
    have hpointBool :=
      (List.all_eq_true.mp hresidueAll) point hpoint
    simpa only [beq_iff_eq] using hpointBool
  let rho : ZMod 6 := residue
  refine ⟨rho, ?_⟩
  have hsubset :
      z180K30FifthFibres36 X i ⊆
        (Finset.univ : Finset (ZMod 36)).filter
          (fun q => z36K30Projection6 q = rho) := by
    intro q hq
    have hqRaw :
        q ∈ ((z180K30RawFibreV63Fix X i hcard).map
          (fun point => (point.val : ZMod 36))).toFinset := by
      rw [z180K30RawFibreV63Fix_toFinset X i hcard]
      exact hq
    rw [List.mem_toFinset] at hqRaw
    rcases List.mem_map.mp hqRaw with ⟨point, hpoint, hpointq⟩
    subst q
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply ZMod.val_injective
    simp [rho, z36K30Projection6_apply, ZMod.cast_eq_val,
      ZMod.val_natCast, Nat.mod_eq_of_lt point.isLt,
      hpointMod point hpoint, Nat.mod_eq_of_lt hresidueLt]
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [z36K30_H_class_card_v66 rho, hcard]

theorem z180_k30_HCosetColumnConcrete_of_catalogue_v66
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6)
    (hcatalogue : Z180K30CatalogueAlternativeV65
      (z180K30RawFibreV63Fix X i hcard)) :
    Z180K30HCosetColumnConcrete X i := by
  have hH := z180_k30_catalogue_alternative_force_H_v65 hcatalogue
  apply z180_k30_HCosetColumnConcrete_of_raw_v66 X i hcard
  exact HCosetB_of_valid_affine_H_v64Fix
    (z180K30RawFibreV63Fix X i hcard) hH.1 hH.2

end

end Fuglede
