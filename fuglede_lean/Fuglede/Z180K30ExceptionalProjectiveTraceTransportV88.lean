import Fuglede.Z180K30ExceptionalProjectiveTransportV86
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Exact trace transport for the K30 projective normalization

The raw Gram trace depends only on the two difference multisets.  Hence it is
unchanged by reordering either marginal or translating either marginal in
`Z/36Z`.  These lemmas let the finite audit work with independently
translation-normalized representatives.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem coeffAdd_right_comm_v88
    (a b c : Coeff) :
    coeffAdd (coeffAdd a b) c = coeffAdd (coeffAdd a c) b := by
  induction a generalizing b c with
  | nil => simp [coeffAdd]
  | cons head tail ih =>
      cases b with
      | nil => simp [coeffAdd]
      | cons bHead bTail =>
          cases c with
          | nil => simp [coeffAdd]
          | cons cHead cTail =>
              change
                ((head + bHead) + cHead) ::
                    coeffAdd (coeffAdd tail bTail) cTail =
                  ((head + cHead) + bHead) ::
                    coeffAdd (coeffAdd tail cTail) bTail
              congr 1
              · omega
              · exact ih bTail cTail

local instance coeffAddRightCommutativeV88 :
    RightCommutative coeffAdd :=
  ⟨coeffAdd_right_comm_v88⟩

theorem coeffSum_eq_of_perm_v88
    {left right : List Coeff} (hperm : left.Perm right) :
    coeffSum left = coeffSum right := by
  exact hperm.foldl_eq coeffZero

theorem energy_eq_of_perm_v88
    {V V' : RawSet} (hperm : V.Perm V') (difference : Nat) :
    energy V difference = energy V' difference := by
  apply coeffSum_eq_of_perm_v88
  exact hperm.flatMap fun v _hv =>
    hperm.map fun w =>
      zetaPower (difference * ((v.val + 36 - w.val) % 36))

set_option maxHeartbeats 1000000 in
theorem gramTraceSquare_eq_of_perm_left_v88
    {U U' : RawSet} (hperm : U.Perm U') (V : RawSet) :
    gramTraceSquare U V = gramTraceSquare U' V := by
  apply coeffSum_eq_of_perm_v88
  exact hperm.flatMap fun u _hu =>
    hperm.map fun w => energy V ((u.val + 36 - w.val) % 36)

theorem gramTraceSquare_eq_of_perm_right_v88
    (U : RawSet) {V V' : RawSet} (hperm : V.Perm V') :
    gramTraceSquare U V = gramTraceSquare U V' := by
  unfold gramTraceSquare
  simp_rw [energy_eq_of_perm_v88 hperm]

@[simp]
theorem cyclicDifference_translate_v88
    (shift left right : RawPoint) :
    ((affinePoint 1 shift left).val + 36 -
        (affinePoint 1 shift right).val) % 36 =
      (left.val + 36 - right.val) % 36 := by
  simp only [affinePoint]
  omega

@[simp]
theorem energy_translate_v88
    (V : RawSet) (shift : RawPoint) (difference : Nat) :
    energy (affineSet 1 shift V) difference = energy V difference := by
  unfold energy affineSet
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro v hv
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply, cyclicDifference_translate_v88]

@[simp]
theorem gramTraceSquare_translate_left_v88
    (U V : RawSet) (shift : RawPoint) :
    gramTraceSquare (affineSet 1 shift U) V = gramTraceSquare U V := by
  unfold gramTraceSquare affineSet
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro u hu
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply, cyclicDifference_translate_v88]

@[simp]
theorem gramTraceSquare_translate_right_v88
    (U V : RawSet) (shift : RawPoint) :
    gramTraceSquare U (affineSet 1 shift V) = gramTraceSquare U V := by
  unfold gramTraceSquare
  simp_rw [energy_translate_v88]

private theorem eraseDups_length_le_v88 :
    ∀ set : RawSet, set.eraseDups.length ≤ set.length
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      apply Nat.succ_le_succ
      exact (eraseDups_length_le_v88
        (tail.filter fun point => !point == head)).trans
          (List.length_filter_le _ _)
termination_by set => set.length
decreasing_by
  exact (List.length_filter_le _ _).trans_lt
    (Nat.lt_succ_self tail.length)

private theorem nodup_of_eraseDups_length_eq_v88
    (set : RawSet) (hlength : set.eraseDups.length = set.length) :
    set.Nodup := by
  induction set with
  | nil => simp
  | cons head tail ih =>
      rw [List.eraseDups_cons] at hlength
      let filtered := tail.filter fun point => !point == head
      have hlength' : filtered.eraseDups.length = tail.length := by
        dsimp only [filtered]
        exact Nat.succ.inj (by simpa only [List.length_cons] using hlength)
      have heraseLe : filtered.eraseDups.length ≤ filtered.length :=
        eraseDups_length_le_v88 filtered
      have hfilterLe : filtered.length ≤ tail.length :=
        List.length_filter_le _ _
      have hfilterLength : filtered.length = tail.length := by
        omega
      have hall : ∀ point ∈ tail, (!point == head) = true :=
        (List.length_filter_eq_length_iff.mp hfilterLength)
      have hhead : head ∉ tail := by
        intro hmem
        have hfalse := hall head hmem
        simp at hfalse
      have hfiltered : filtered = tail := by
        exact List.filter_eq_self.mpr hall
      have htailLength : tail.eraseDups.length = tail.length := by
        simpa only [hfiltered] using hlength'
      exact List.Nodup.cons hhead (ih htailLength)

theorem validSixSetB_nodup_v88
    {set : RawSet} (hvalid : validSixSetB set = true) : set.Nodup := by
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq] at hvalid
  apply nodup_of_eraseDups_length_eq_v88 set
  omega

theorem validSixSetB_length_v88
    {set : RawSet} (hvalid : validSixSetB set = true) : set.length = 6 := by
  simp only [validSixSetB, Bool.and_eq_true, beq_iff_eq] at hvalid
  exact hvalid.1

theorem perm_of_rawSetEqB_of_valid_v88
    {left right : RawSet}
    (hleft : validSixSetB left = true)
    (hright : validSixSetB right = true)
    (heq : rawSetEqB left right = true) :
    left.Perm right := by
  have hleftNodup := validSixSetB_nodup_v88 hleft
  have hrightNodup := validSixSetB_nodup_v88 hright
  have hleftLength := validSixSetB_length_v88 hleft
  have hrightLength := validSixSetB_length_v88 hright
  simp only [rawSetEqB, Bool.and_eq_true, beq_iff_eq] at heq
  have hsubset : left.toFinset ⊆ right.toFinset := by
    intro point hpoint
    rw [List.mem_toFinset] at hpoint ⊢
    exact of_decide_eq_true
      ((List.all_eq_true.mp heq.2) point hpoint)
  have hcardLeft : left.toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup hleftNodup, hleftLength]
  have hcardRight : right.toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup hrightNodup, hrightLength]
  have hfinset : left.toFinset = right.toFinset :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
  intro point
  simpa using (Finset.ext_iff.mp hfinset point)

#print axioms gramTraceSquare_translate_left_v88
#print axioms gramTraceSquare_translate_right_v88
#print axioms perm_of_rawSetEqB_of_valid_v88

end Fuglede.Z180K30ExceptionalRawV2
