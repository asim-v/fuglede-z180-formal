import Fuglede.Z180K30ExceptionalRawCoreV2
import Fuglede.Z180K30ProjectedFibreFourierV57
import Mathlib.Tactic

/-!
# Faithful raw encoding of the six-point K30 fibres

The exact exceptional certificate uses lists of `Fin 36`.  This module turns
the canonical enumeration of a genuine projected fibre into such a list and
proves that it is a valid six-set with exactly the original `ZMod 36` support.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

def z180K30RawPointV63 (q : ZMod 36) : RawPoint :=
  ⟨q.val, q.val_lt⟩

@[simp]
theorem z180K30RawPointV63_val (q : ZMod 36) :
    ((z180K30RawPointV63 q).val : ZMod 36) = q := by
  exact ZMod.natCast_zmod_val q

noncomputable def z180K30RawFibreV63
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) : RawSet :=
  List.ofFn fun k : Fin 6 =>
    z180K30RawPointV63 (z180K30ProjectedFibreEnumV57 X i hcard k)

theorem z180K30RawFibreV63_nodup
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    (z180K30RawFibreV63 X i hcard).Nodup := by
  apply List.nodup_ofFn.mpr
  intro k l hkl
  apply z180K30ProjectedFibreEnumV57_injective X i hcard
  apply ZMod.val_injective
  exact congrArg Fin.val hkl

theorem z180K30RawFibreV63_validSixSetB
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    validSixSetB (z180K30RawFibreV63 X i hcard) = true := by
  unfold validSixSetB
  rw [List.eraseDups_eq_self.mpr
    (z180K30RawFibreV63_nodup X i hcard)]
  simp [z180K30RawFibreV63]

theorem z180K30RawFibreV63_toFinset
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    ((z180K30RawFibreV63 X i hcard).map
      (fun p => (p.val : ZMod 36))).toFinset =
        z180K30FifthFibres36 X i := by
  classical
  ext y
  constructor
  · intro hy
    rw [List.mem_toFinset] at hy
    rcases List.mem_map.mp hy with ⟨p, hp, hpy⟩
    rcases List.mem_ofFn.mp hp with ⟨k, rfl⟩
    have hmem := z180K30ProjectedFibreEnumV57_mem X i hcard k
    simpa only [z180K30RawPointV63_val] using hpy ▸ hmem
  · intro hy
    obtain ⟨k, hk⟩ :=
      z180K30ProjectedFibreEnumV57_surjective X i hcard y hy
    rw [List.mem_toFinset]
    apply List.mem_map.mpr
    refine ⟨z180K30RawPointV63
      (z180K30ProjectedFibreEnumV57 X i hcard k), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨k, rfl⟩
    · simpa only [z180K30RawPointV63_val] using hk

#print axioms z180K30RawFibreV63_validSixSetB
#print axioms z180K30RawFibreV63_toFinset

end
end Fuglede
