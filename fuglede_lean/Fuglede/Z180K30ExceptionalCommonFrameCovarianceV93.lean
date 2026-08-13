import Fuglede.Z180K30ExceptionalFramedStarInterfacesV84Fix2
import Fuglede.Z180K30ExceptionalCommonFrameTraceV93
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91
import Mathlib.Data.List.GetD

/-!
# Exact same-unit common-frame covariance for the K30 star (V93)

If the framed column is the affine image `unit * representative + translation`,
then the row belonging to the same Fourier frame is `unit * U` (with zero row
translation).  The inverse-unit normalization in the V92 drafts has the wrong
orientation for `gramTraceSquare_affine_covariant_v90`.

Besides the trace statement used by the V91 row classifier, this module proves
the coefficient-level covariance needed by the five-Gram identity.  The latter
keeps track of a possible reordering between the explicit affine image and the
original raw column list through `List.Perm.idxBij`.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem zetaPower_scale_product_v93
    (unit difference otherDifference : Nat) :
    zetaPower (((unit * difference) % 36) * otherDifference) =
      zetaPower (difference * ((unit * otherDifference) % 36)) := by
  unfold zetaPower
  congr 1
  have hleft :
      ((unit * difference) % 36) * otherDifference ≡
        unit * difference * otherDifference [MOD 36] :=
    (Nat.mod_modEq _ _).mul_right _
  have hright :
      difference * (unit * otherDifference) ≡
        difference * ((unit * otherDifference) % 36) [MOD 36] :=
    (Nat.mod_modEq _ _).symm.mul_left _
  exact hleft.trans ((by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hright) :
      unit * difference * otherDifference ≡
        difference * ((unit * otherDifference) % 36) [MOD 36])

/-- Dilation of the row by `unit` is exactly the same Gram operation as
dilation (and arbitrary translation) of the column by the same unit. -/
theorem gram_affine_covariant_v93
    (U V : RawSet) (unit translation : RawPoint) :
    gram (affineSet unit 0 U) V =
      gram U (affineSet unit translation V) := by
  unfold gram affineSet
  simp only [List.flatMap_map, List.map_map, Function.comp_apply]
  apply List.flatMap_congr
  intro row hrow
  apply List.map_congr_left
  intro column hcolumn
  congr 1
  apply List.map_congr_left
  intro point hpoint
  rw [cyclicDifference_affine_v90 unit translation column row]
  simpa [affinePoint] using
    zetaPower_scale_product_v93 unit.val point.val
      ((column.val + 36 - row.val) % 36)

private theorem getD_flatMap_uniform_v93
    {alpha beta : Type} (values : List alpha) (block : alpha → List beta)
    (blockLength row column : Nat) (default : beta)
    (hlength : ∀ value ∈ values, (block value).length = blockLength)
    (hrow : row < values.length) (hcolumn : column < blockLength) :
    (values.flatMap block).getD (row * blockLength + column) default =
      (block values[row]).getD column default := by
  induction values generalizing row with
  | nil => simp at hrow
  | cons head tail ih =>
      cases row with
      | zero =>
          have hhead : column < (block head).length := by
            rw [hlength head (by simp)]
            exact hcolumn
          simpa only [List.flatMap_cons, Nat.zero_mul, zero_add,
            List.getElem_cons_zero] using
            List.getD_append (block head) (tail.flatMap block)
              default column hhead
      | succ row =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hrow
          have hheadLength : (block head).length = blockLength :=
            hlength head (by simp)
          have htailLength :
              ∀ value ∈ tail, (block value).length = blockLength := by
            intro value hvalue
            exact hlength value (by simp [hvalue])
          have hrowTail : row < tail.length := by
            exact hrow
          have hright :
              (block head).length ≤
                Nat.succ row * blockLength + column := by
            rw [hheadLength]
            rw [Nat.succ_mul]
            omega
          have hindex :
              Nat.succ row * blockLength + column -
                  (block head).length =
                row * blockLength + column := by
            rw [hheadLength]
            rw [Nat.succ_mul]
            omega
          rw [List.flatMap_cons,
            List.getD_append_right _ _ _ _ hright, hindex]
          simpa only [List.getElem_cons_succ] using
            ih (row := row) htailLength hrowTail

private theorem gram_getD_entry_v93
    (U V : RawSet) (row column : Nat)
    (hrow : row < V.length) (hcolumn : column < V.length) :
    (gram U V).getD (row * V.length + column) coeffZero =
      coeffSum (U.map fun point =>
        zetaPower
          (point.val *
            ((V[column].val + 36 - V[row].val) % 36))) := by
  unfold gram
  rw [getD_flatMap_uniform_v93 V
    (fun rowPoint => V.map fun columnPoint =>
      coeffSum (U.map fun point =>
        zetaPower
          (point.val *
            ((columnPoint.val + 36 - rowPoint.val) % 36))))
    V.length row column coeffZero]
  · rw [List.getD_eq_getElem
      (l := V.map fun columnPoint =>
        coeffSum (U.map fun point =>
          zetaPower
            (point.val *
              ((columnPoint.val + 36 - V[row].val) % 36))))
      (d := coeffZero) (by simpa using hcolumn)]
    simp only [List.getElem_map]
  · intro value hvalue
    simp
  · exact hrow
  · exact hcolumn

/-- A simultaneous row/column reordering of the column list transports an
individual Gram coefficient along the induced bijection of indices. -/
theorem gramCoefficientV2_perm_entry_v93
    (U : RawSet) {left right : RawSet} (hperm : left.Perm right)
    (row column : Fin left.length) (coefficient : Nat) :
    gramCoefficientV2 (gram U left)
        (row.val * left.length + column.val) coefficient =
      gramCoefficientV2 (gram U right)
        ((hperm.idxBij row).val * right.length +
          (hperm.idxBij column).val) coefficient := by
  unfold gramCoefficientV2
  rw [gram_getD_entry_v93 U left row.val column.val row.isLt column.isLt]
  rw [gram_getD_entry_v93 U right
    (hperm.idxBij row).val (hperm.idxBij column).val
    (hperm.idxBij row).isLt (hperm.idxBij column).isLt]
  rw [hperm.getElem_idxBij_eq_getElem row,
    hperm.getElem_idxBij_eq_getElem column]

private theorem gramTarget30_offDiagonal_v93
    (row column : Nat) (hrow : row < 6) (hcolumn : column < 6)
    (hne : row ≠ column) (coefficient : Nat) :
    gramCoefficientV2 gramTarget30 (row * 6 + column) coefficient = 0 := by
  have hindex : row * 6 + column < 36 := by omega
  have hdiag :
      (row * 6 + column) / 6 ≠ (row * 6 + column) % 6 := by
    have hdiv : (row * 6 + column) / 6 = row := by omega
    have hmod : (row * 6 + column) % 6 = column := by omega
    omega
  unfold gramCoefficientV2
  rw [List.getD_eq_getElem (l := gramTarget30) (d := coeffZero)
    (by simpa [gramTarget30] using hindex)]
  simp only [gramTarget30, List.getElem_map, List.getElem_range]
  rw [if_neg hdiag]
  by_cases hcoefficient : coefficient < 12
  · interval_cases coefficient <;> rfl
  · rw [List.getD_eq_default (l := coeffZero) (d := 0)
      (by simpa [coeffZero] using Nat.le_of_not_gt hcoefficient)]

private theorem gram_entry_wf_v93
    (U V : RawSet) (index : Nat) (hindex : index < 36) :
    CoeffWF ((gram U V).getD index coeffZero) := by
  by_cases hmem : index < (gram U V).length
  · apply gram_entry_wf_v76Fix
    rw [List.getD_eq_getElem (l := gram U V) (d := coeffZero) hmem]
    exact List.getElem_mem _
  · rw [List.getD_eq_default (l := gram U V) (d := coeffZero)
      (Nat.le_of_not_gt hmem)]
    exact coeffZero_wf_v71Fix

private theorem coeffAdd_getD_v93
    {left right : Coeff} (hleft : CoeffWF left) (hright : CoeffWF right)
    (coefficient : Nat) :
    (coeffAdd left right).getD coefficient 0 =
      left.getD coefficient 0 + right.getD coefficient 0 := by
  by_cases hcoefficient : coefficient < 12
  · have hleftLength : coefficient < left.length := by
      change left.length = 12 at hleft
      omega
    have hrightLength : coefficient < right.length := by
      change right.length = 12 at hright
      omega
    induction coefficient generalizing left right with
    | zero => cases left <;> cases right <;> simp_all [coeffAdd]
    | succ coefficient ih =>
        cases left <;> cases right <;> simp_all [coeffAdd, CoeffWF]
  · have hleftLength : left.length ≤ coefficient := by
      change left.length = 12 at hleft
      omega
    have hrightLength : right.length ≤ coefficient := by
      change right.length = 12 at hright
      omega
    have haddLength : (coeffAdd left right).length ≤ coefficient := by
      rw [coeffAdd_length_v71Fix
        (by simpa [CoeffWF] using hleft)
        (by simpa [CoeffWF] using hright)]
      exact Nat.le_of_not_gt hcoefficient
    rw [List.getD_eq_default _ _ haddLength,
      List.getD_eq_default _ _ hleftLength,
      List.getD_eq_default _ _ hrightLength]
    omega

private theorem gramAdd_getD_entry_v93
    (left right : Gram) (index : Nat)
    (hindex : index < left.length) (hindexRight : index < right.length) :
    (gramAdd left right).getD index coeffZero =
      coeffAdd (left.getD index coeffZero)
        (right.getD index coeffZero) := by
  induction index generalizing left right with
  | zero => cases left <;> cases right <;> simp_all [gramAdd]
  | succ index ih => cases left <;> cases right <;> simp_all [gramAdd]

private theorem gramAdd_entry_wf_v93
    (left right : Gram) (index : Nat)
    (hindex : index < left.length) (hindexRight : index < right.length)
    (hleft : CoeffWF (left.getD index coeffZero))
    (hright : CoeffWF (right.getD index coeffZero)) :
    CoeffWF ((gramAdd left right).getD index coeffZero) := by
  rw [gramAdd_getD_entry_v93 left right index hindex hindexRight]
  exact coeffAdd_wf_v71Fix hleft hright

private theorem gramAdd_entry_coefficient_v93
    (left right : Gram) (index coefficient : Nat)
    (hindex : index < left.length) (hindexRight : index < right.length)
    (hleft : CoeffWF (left.getD index coeffZero))
    (hright : CoeffWF (right.getD index coeffZero)) :
    gramCoefficientV2 (gramAdd left right) index coefficient =
      gramCoefficientV2 left index coefficient +
        gramCoefficientV2 right index coefficient := by
  unfold gramCoefficientV2
  rw [gramAdd_getD_entry_v93 left right index hindex hindexRight]
  exact coeffAdd_getD_v93 hleft hright coefficient

private theorem gramAdd_getD_wf_v93
    (left right : Gram) (index : Nat)
    (hindex : index < left.length) (hindexRight : index < right.length)
    (hleft : CoeffWF (left.getD index coeffZero))
    (hright : CoeffWF (right.getD index coeffZero)) :
    CoeffWF ((gramAdd left right).getD index coeffZero) := by
  have hentry :
      (gramAdd left right).getD index coeffZero =
        coeffAdd (left.getD index coeffZero)
          (right.getD index coeffZero) := by
    induction index generalizing left right with
    | zero => cases left <;> cases right <;> simp_all [gramAdd]
    | succ index ih => cases left <;> cases right <;> simp_all [gramAdd]
  rw [hentry]
  exact coeffAdd_wf_v71Fix hleft hright

private theorem gramZero_entry_coefficient_v93
    (index coefficient : Nat) (hindex : index < 36) :
    gramCoefficientV2 gramZero index coefficient = 0 := by
  unfold gramCoefficientV2
  rw [List.getD_eq_getElem (l := gramZero) (d := coeffZero)
    (by simpa [gramZero] using hindex)]
  simp only [gramZero, List.getElem_replicate]
  by_cases hcoefficient : coefficient < 12
  · interval_cases coefficient <;> rfl
  · rw [List.getD_eq_default (l := coeffZero) (d := 0)
      (by simpa [coeffZero] using Nat.le_of_not_gt hcoefficient)]

private theorem fiveGramSum_coefficient_v93
    (U : Fin 5 → RawSet) (V : RawSet)
    (index coefficient : Nat) (hindex : index < 36)
    (hlength : V.length = 6) :
    gramCoefficientV2 (gramSum (List.ofFn fun i => gram (U i) V))
        index coefficient =
      z180K30FiveGramCoefficientSumV4 U V index coefficient := by
  have hgram (i : Fin 5) : CoeffWF ((gram (U i) V).getD index coeffZero) :=
    gram_entry_wf_v93 (U i) V index hindex
  have hzero : CoeffWF (gramZero.getD index coeffZero) := by
    have hz : gramZero.getD index coeffZero = coeffZero := by
      unfold gramZero
      exact List.getD_replicate (x := coeffZero) (y := coeffZero) hindex
    rw [hz]
    exact coeffZero_wf_v71Fix
  have hacc0 :
      CoeffWF ((gramAdd gramZero (gram (U 0) V)).getD index coeffZero) :=
    gramAdd_getD_wf_v93 gramZero (gram (U 0) V) index
      (by simpa [gramZero] using hindex)
      (by simpa [gram, hlength] using hindex) hzero (hgram 0)
  have hacc1 :
      CoeffWF
        ((gramAdd (gramAdd gramZero (gram (U 0) V))
          (gram (U 1) V)).getD index coeffZero) :=
    gramAdd_getD_wf_v93 (gramAdd gramZero (gram (U 0) V))
      (gram (U 1) V) index
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex) hacc0 (hgram 1)
  have hacc2 :
      CoeffWF
        ((gramAdd
          (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
          (gram (U 2) V)).getD index coeffZero) :=
    gramAdd_getD_wf_v93
      (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
      (gram (U 2) V) index
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex) hacc1 (hgram 2)
  have hacc3 :
      CoeffWF
        ((gramAdd
          (gramAdd
            (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
            (gram (U 2) V)) (gram (U 3) V)).getD index coeffZero) :=
    gramAdd_getD_wf_v93
      (gramAdd
        (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
        (gram (U 2) V))
      (gram (U 3) V) index
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex) hacc2 (hgram 3)
  have hofFn :
      (List.ofFn fun i : Fin 5 => gram (U i) V) =
        [gram (U 0) V, gram (U 1) V, gram (U 2) V,
          gram (U 3) V, gram (U 4) V] := by
    change [gram (U 0) V, gram (U 1) V, gram (U 2) V,
      gram (U 3) V, gram (U 4) V] = _
    rfl
  unfold gramSum z180K30FiveGramCoefficientSumV4
  rw [hofFn]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [gramAdd_entry_coefficient_v93
      (gramAdd
        (gramAdd
          (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
          (gram (U 2) V)) (gram (U 3) V))
      (gram (U 4) V) index coefficient
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex)
      hacc3 (hgram 4),
    gramAdd_entry_coefficient_v93
      (gramAdd
        (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
        (gram (U 2) V)) (gram (U 3) V) index coefficient
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex)
      hacc2 (hgram 3),
    gramAdd_entry_coefficient_v93
      (gramAdd (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V))
      (gram (U 2) V) index coefficient
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex)
      hacc1 (hgram 2),
    gramAdd_entry_coefficient_v93
      (gramAdd gramZero (gram (U 0) V)) (gram (U 1) V)
      index coefficient
      (by simpa [gramAdd, gramZero, gram, hlength] using hindex)
      (by simpa [gram, hlength] using hindex)
      hacc0 (hgram 1),
    gramAdd_entry_coefficient_v93 gramZero (gram (U 0) V)
      index coefficient
      (by simpa [gramZero] using hindex)
      (by simpa [gram, hlength] using hindex) hzero (hgram 0),
    gramZero_entry_coefficient_v93 index coefficient hindex]
  omega

/-- Every off-diagonal coefficient of an exact five-Gram star sums to zero.
The indices are allowed to depend on a permutation of the six-point column. -/
theorem fiveGramStar_offDiagonalCoefficientSum_zero_v93
    (U : Fin 5 → RawSet) (V : RawSet)
    (hstar : fiveGramStarB U V = true)
    (row column : Fin V.length) (hne : row ≠ column)
    (coefficient : Nat) :
    z180K30FiveGramCoefficientSumV4 U V
        (row.val * 6 + column.val) coefficient = 0 := by
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  have hlength : V.length = 6 := validSixSetB_length_v88 hvalidV
  have hrow : row.val < 6 := by simpa [hlength] using row.isLt
  have hcolumn : column.val < 6 := by simpa [hlength] using column.isLt
  have htarget := gramTarget30_offDiagonal_v93
    row.val column.val hrow hcolumn (by
      intro heq
      apply hne
      exact Fin.ext heq) coefficient
  have hcoefficient := fiveGramStar_gramCoefficient_eq_v2 U V
    (row.val * 6 + column.val) coefficient hstar
  rw [htarget] at hcoefficient
  rw [fiveGramSum_coefficient_v93 U V
    (row.val * 6 + column.val) coefficient (by omega) hlength] at hcoefficient
  exact hcoefficient

/-- The coefficient sum of the five rows in the explicit same-unit frame is
zero at every off-diagonal representative entry. -/
theorem fiveGramStar_commonFrameCoefficientSum_zero_v93
    (U : Fin 5 → RawSet) (V representative : RawSet)
    (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hvalidRepresentative : validSixSetB representative = true)
    (hframe :
      rawSetEqB (affineSet unit translation representative) V = true)
    (hstar : fiveGramStarB U V = true)
    (row column : Nat)
    (hrow : row < representative.length)
    (hcolumn : column < representative.length)
    (hne : row ≠ column) (coefficient : Nat) :
    z180K30FiveGramCoefficientSumV4
        (fun i => affineSet unit 0 (U i)) representative
        (row * 6 + column) coefficient = 0 := by
  let affineRepresentative := affineSet unit translation representative
  have hvalidV : validSixSetB V = true :=
    (fiveGramStar_components_v82 U V hstar 0).2.1
  have hvalidAffine : validSixSetB affineRepresentative = true := by
    exact validSixSetB_affine_of_unit_v85Fix3
      unit translation representative hunit hvalidRepresentative
  have hperm : affineRepresentative.Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  have hrepresentativeLength : representative.length = 6 :=
    validSixSetB_length_v88 hvalidRepresentative
  have haffineLength : affineRepresentative.length = 6 := by
    simpa [affineRepresentative, affineSet] using hrepresentativeLength
  have hVLength : V.length = 6 := validSixSetB_length_v88 hvalidV
  let affineRow : Fin affineRepresentative.length :=
    ⟨row, by simpa [affineRepresentative, affineSet] using hrow⟩
  let affineColumn : Fin affineRepresentative.length :=
    ⟨column, by simpa [affineRepresentative, affineSet] using hcolumn⟩
  let originalRow : Fin V.length := hperm.idxBij affineRow
  let originalColumn : Fin V.length := hperm.idxBij affineColumn
  have hneAffine : affineRow ≠ affineColumn := by
    intro heq
    apply hne
    exact congrArg Fin.val heq
  have hneOriginal : originalRow ≠ originalColumn := by
    intro heq
    exact hneAffine (hperm.idxBij_injective heq)
  have horiginal := fiveGramStar_offDiagonalCoefficientSum_zero_v93
    U V hstar originalRow originalColumn hneOriginal coefficient
  have hentry (i : Fin 5) :
      gramCoefficientV2
          (gram (affineSet unit 0 (U i)) representative)
          (row * 6 + column) coefficient =
        gramCoefficientV2 (gram (U i) V)
          (originalRow.val * 6 + originalColumn.val) coefficient := by
    rw [gram_affine_covariant_v93]
    simpa [affineRepresentative, affineRow, affineColumn,
      originalRow, originalColumn, haffineLength, hVLength,
      hrepresentativeLength] using
      gramCoefficientV2_perm_entry_v93
        (U i) hperm affineRow affineColumn coefficient
  unfold z180K30FiveGramCoefficientSumV4 at horiginal ⊢
  rw [hentry 0, hentry 1, hentry 2, hentry 3, hentry 4]
  exact horiginal

/-- Exact common-frame form of the V4 star-coordinate obligation. -/
theorem fiveGramStar_commonFrameCoordinates_v93
    (U : Fin 5 → RawSet) (V : RawSet)
    (o : Fin 8) (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hframe : rawSetEqB
      (affineSet unit translation (z180K30ExceptionalOrbitColumnV4 o)) V = true)
    (hstar : fiveGramStarB U V = true) :
    Z180K30ExceptionalOrbitStarCoordinatesV4 o
      (fun i => affineSet unit 0 (U i)) := by
  have hvalidRepresentative :
      validSixSetB (z180K30ExceptionalOrbitColumnV4 o) = true := by
    fin_cases o <;> decide
  fin_cases o
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 0) unit translation
      hunit hvalidRepresentative hframe hstar 0 3 (by decide) (by decide)
      (by decide) 0
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 1) unit translation
      hunit hvalidRepresentative hframe hstar 0 3 (by decide) (by decide)
      (by decide) 0
  · constructor
    · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
        U V (z180K30ExceptionalOrbitColumnV4 2) unit translation
        hunit hvalidRepresentative hframe hstar 0 2 (by decide) (by decide)
        (by decide) 0
    · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
        U V (z180K30ExceptionalOrbitColumnV4 2) unit translation
        hunit hvalidRepresentative hframe hstar 0 2 (by decide) (by decide)
        (by decide) 6
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 3) unit translation
      hunit hvalidRepresentative hframe hstar 0 3 (by decide) (by decide)
      (by decide) 0
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 4) unit translation
      hunit hvalidRepresentative hframe hstar 0 3 (by decide) (by decide)
      (by decide) 0
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 5) unit translation
      hunit hvalidRepresentative hframe hstar 0 3 (by decide) (by decide)
      (by decide) 0
  · exact fiveGramStar_commonFrameCoefficientSum_zero_v93
      U V (z180K30ExceptionalOrbitColumnV4 6) unit translation
      hunit hvalidRepresentative hframe hstar 0 2 (by decide) (by decide)
      (by decide) 0
  · trivial

#print axioms gram_affine_covariant_v93
#print axioms fiveGramStar_commonFrameCoordinates_v93

end Fuglede.Z180K30ExceptionalRawV2
