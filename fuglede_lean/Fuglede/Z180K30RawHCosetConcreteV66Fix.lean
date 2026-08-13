import Fuglede.Z180K30ExceptionalRawFibreV63Fix
import Fuglede.Z180K30ExceptionalAffineHBridgeV64Fix
import Fuglede.Z180K30CatalogueAlternativeV65
import Fuglede.Z180K30ExceptionalHCoordinateCoreV5
import Mathlib.Tactic

/-!
# From the raw exceptional H certificate to a concrete ZMod 36 fibre

The raw list used by the finite certificate is a faithful enumeration of the
actual projected fibre.  Consequently the Boolean assertion that all six raw
points lie in one residue class modulo six is exactly the concrete H-coset
condition needed by the exceptional tiling bridge.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

private theorem z180K30_projection6_class_card_v66Fix
    (rho : ZMod 6) :
    ((Finset.univ : Finset (ZMod 36)).filter
      (fun q => z36K30Projection6 q = rho)).card = 6 := by
  fin_cases rho <;> decide

theorem z180_k30_HCosetColumnConcrete_of_raw_v66Fix
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6)
    (hH : HCosetB (z180K30RawFibreV63Fix X i hcard) = true) :
    Z180K30HCosetColumnConcrete X i := by
  have hvalid := z180K30RawFibreV63Fix_validSixSetB X i hcard
  rw [HCosetB, hvalid, Bool.true_and] at hH
  rcases List.any_eq_true.mp hH with
    ⟨residue, hresidueRange, hAll⟩
  let rho : ZMod 6 := residue
  refine ⟨rho, ?_⟩
  let target : Finset (ZMod 36) :=
    (Finset.univ : Finset (ZMod 36)).filter
      (fun q => z36K30Projection6 q = rho)
  change z180K30FifthFibres36 X i = target
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    have hsupport := z180K30RawFibreV63Fix_toFinset X i hcard
    have hqRaw : q ∈
        ((z180K30RawFibreV63Fix X i hcard).map
          (fun p => (p.val : ZMod 36))).toFinset := by
      rw [hsupport]
      exact hq
    rw [List.mem_toFinset] at hqRaw
    rcases List.mem_map.mp hqRaw with ⟨p, hp, hpq⟩
    have hdecide := (List.all_eq_true.mp hAll) p hp
    have hnat : p.val % 6 = residue := of_decide_eq_true hdecide
    have hrange : residue < 6 := List.mem_range.mp hresidueRange
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ q, ?_⟩
    rw [z36K30Projection6_apply]
    change (ZMod.cast q : ZMod 6) = rho
    rw [← hpq]
    apply ZMod.val_injective
    simpa [rho, hnat, Nat.mod_eq_of_lt hrange]
  · have htarget : target.card = 6 := by
      exact z180K30_projection6_class_card_v66Fix rho
    rw [htarget, hcard]

theorem z180_k30_HCosetColumnConcrete_of_catalogue_v66Fix
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6)
    (hcat : Z180K30CatalogueAlternativeV65
      (z180K30RawFibreV63Fix X i hcard)) :
    Z180K30HCosetColumnConcrete X i := by
  have hforce := z180_k30_catalogue_alternative_force_H_v65 hcat
  have hraw : HCosetB (z180K30RawFibreV63Fix X i hcard) = true :=
    HCosetB_of_valid_affine_H_v64Fix _ hforce.1 hforce.2
  exact z180_k30_HCosetColumnConcrete_of_raw_v66Fix X i hcard hraw

#print axioms z180_k30_HCosetColumnConcrete_of_raw_v66Fix
#print axioms z180_k30_HCosetColumnConcrete_of_catalogue_v66Fix

end
end Fuglede
