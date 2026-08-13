import Fuglede.Z180K30ExceptionalRawCoreV2
import Fuglede.Z180K30ProjectedFibreFourierV57
import Mathlib.Tactic

/-!
# Faithful raw encoding of the six-point K30 fibres

This repaired V63 module avoids relying on verification lemmas for
`List.eraseDups`, whose core API intentionally exposes only a minimal surface.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

def z180K30RawPointV63Fix (q : ZMod 36) : RawPoint :=
  ⟨q.val, q.val_lt⟩

@[simp]
theorem z180K30RawPointV63Fix_val (q : ZMod 36) :
    ((z180K30RawPointV63Fix q).val : ZMod 36) = q := by
  exact ZMod.natCast_zmod_val q

noncomputable def z180K30RawFibreV63Fix
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) : RawSet :=
  List.ofFn fun k : Fin 6 =>
    z180K30RawPointV63Fix (z180K30ProjectedFibreEnumV57 X i hcard k)

theorem z180K30RawFibreV63Fix_nodup
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    (z180K30RawFibreV63Fix X i hcard).Nodup := by
  apply List.nodup_ofFn.mpr
  intro k l hkl
  apply z180K30ProjectedFibreEnumV57_injective X i hcard
  apply ZMod.val_injective
  exact congrArg Fin.val hkl

private theorem eraseDups_eq_self_of_nodup_v63Fix
    {l : List RawPoint} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at h
      have hfilter : (l.filter fun b => !b == a) = l := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hba : b ≠ a := by
          intro hba
          apply h.1
          simpa [hba] using hb
        simp [hba]
      rw [List.eraseDups_cons, hfilter, ih h.2]

theorem z180K30RawFibreV63Fix_validSixSetB
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    validSixSetB (z180K30RawFibreV63Fix X i hcard) = true := by
  unfold validSixSetB
  rw [eraseDups_eq_self_of_nodup_v63Fix
    (z180K30RawFibreV63Fix_nodup X i hcard)]
  simp [z180K30RawFibreV63Fix]

theorem z180K30RawFibreV63Fix_toFinset
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    ((z180K30RawFibreV63Fix X i hcard).map
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
    rw [z180K30RawPointV63Fix_val] at hpy
    exact hpy ▸ hmem
  · intro hy
    obtain ⟨k, hk⟩ :=
      z180K30ProjectedFibreEnumV57_surjective X i hcard y hy
    rw [List.mem_toFinset]
    apply List.mem_map.mpr
    refine ⟨z180K30RawPointV63Fix
      (z180K30ProjectedFibreEnumV57 X i hcard k), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨k, rfl⟩
    · simpa only [z180K30RawPointV63Fix_val] using hk

#print axioms z180K30RawFibreV63Fix_validSixSetB
#print axioms z180K30RawFibreV63Fix_toFinset

end
end Fuglede
