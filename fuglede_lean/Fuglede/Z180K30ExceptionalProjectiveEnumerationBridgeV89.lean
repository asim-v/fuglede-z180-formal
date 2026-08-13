import Fuglede.Z180K30ExceptionalProjectiveAffineInverseV89
import Fuglede.Z180K30ExceptionalProjectiveAuditBlocksV89
import Fuglede.Z180K30ExceptionalProjectiveDivisorV88
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Abstract normalization into the finite projective enumeration

This module contains no large computation.  It canonically reorders the two
independently translated marginals, proves that the projective side occurs in
`normalizedProjectiveVChoicesV88`, and proves that the other side occurs in
`normalizedProjectiveUChoicesV88`.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def canonicalWithinV89 (domain set : RawSet) : RawSet :=
  domain.filter fun point => decide (point ∈ set)

theorem canonicalWithinV89_sublist (domain set : RawSet) :
    List.Sublist (canonicalWithinV89 domain set) domain := by
  exact List.filter_sublist

theorem canonicalWithinV89_mem_iff
    (domain set : RawSet)
    (hsubset : ∀ point ∈ set, point ∈ domain)
    (point : RawPoint) :
    point ∈ canonicalWithinV89 domain set ↔ point ∈ set := by
  rw [canonicalWithinV89, List.mem_filter]
  constructor
  · exact fun h => of_decide_eq_true h.2
  · intro hpoint
    exact ⟨hsubset point hpoint, decide_eq_true hpoint⟩

theorem canonicalWithinV89_perm
    (domain set : RawSet) (hdomain : domain.Nodup) (hset : set.Nodup)
    (hsubset : ∀ point ∈ set, point ∈ domain) :
    (canonicalWithinV89 domain set).Perm set := by
  apply (List.perm_ext_iff_of_nodup (hdomain.filter _) hset).mpr
  intro point
  exact canonicalWithinV89_mem_iff domain set hsubset point

theorem rawUniverse_nodup_v89 : rawUniverse.Nodup := by
  simpa [rawUniverse] using List.nodup_finRange 36

theorem baseForDivisor_nodup_v89 (divisor : Nat) :
    (baseForDivisor divisor).Nodup := by
  exact rawUniverse_nodup_v89.filter _

theorem normalizedProjectiveClassDomainV88_nodup_v89
    (divisor : Nat) (selection : List Nat) :
    (normalizedProjectiveClassDomainV88 divisor selection).Nodup := by
  exact rawUniverse_nodup_v89.filter _

def translatedResidueV89
    (modulus : Nat) (shift : RawPoint) (residue : Nat) : Nat :=
  (residue + shift.val % modulus) % modulus

theorem affinePoint_mod_of_dvd_v89
    (modulus : Nat) (hmodulus : modulus ∣ 36)
    (shift point : RawPoint) :
    (affinePoint 1 shift point).val % modulus =
      translatedResidueV89 modulus shift (point.val % modulus) := by
  simp only [affinePoint, translatedResidueV89]
  rw [Nat.mod_mod_of_dvd _ hmodulus, Nat.add_mod]
  simp

theorem normalizedProjectiveClassSelectionsV88_singleton_mem_v89
    (divisor residue : Nat)
    (hresidue : residue < 36 / divisor) :
    [residue] ∈ normalizedProjectiveClassSelectionsV88 divisor := by
  rw [normalizedProjectiveClassSelectionsV88, List.mem_append]
  exact Or.inl (List.mem_map.mpr
    ⟨residue, List.mem_range.mpr hresidue, rfl⟩)

theorem normalizedProjectiveClassSelectionsV88_pair_mem_v89
    (divisor first second : Nat)
    (hfirst : first < 36 / divisor)
    (hsecond : second < 36 / divisor) :
    [first, second] ∈ normalizedProjectiveClassSelectionsV88 divisor := by
  rw [normalizedProjectiveClassSelectionsV88, List.mem_append]
  apply Or.inr
  apply List.mem_flatMap.mpr
  exact ⟨first, List.mem_range.mpr hfirst,
    List.mem_map.mpr
      ⟨second, List.mem_range.mpr hsecond, rfl⟩⟩

private theorem supported_modulus_pos_v89
    (divisor : Nat)
    (hdivisor : divisor = 3 ∨ divisor = 4 ∨ divisor = 6) :
    0 < 36 / divisor := by
  rcases hdivisor with rfl | rfl | rfl <;> decide

private theorem supported_modulus_dvd_thirtySix_v89
    (divisor : Nat)
    (hdivisor : divisor = 3 ∨ divisor = 4 ∨ divisor = 6) :
    36 / divisor ∣ 36 := by
  rcases hdivisor with rfl | rfl | rfl <;> norm_num

private theorem exists_translated_class_selection_v89
    (divisor : Nat)
    (hdivisor : divisor = 3 ∨ divisor = 4 ∨ divisor = 6)
    (head : RawPoint) (tail : List RawPoint)
    (hclasses : classCount (head :: tail) (36 / divisor) ≤ 2) :
    ∃ selection ∈ normalizedProjectiveClassSelectionsV88 divisor,
      ∀ point ∈ head :: tail,
        translatedResidueV89 (36 / divisor) (-head)
            (point.val % (36 / divisor)) ∈ selection := by
  let modulus := 36 / divisor
  let residues :=
    ((head :: tail).map fun point => point.val % modulus).eraseDups
  have hlength : residues.length ≤ 2 := by
    simpa only [residues, modulus, classCount] using hclasses
  have hhead : head.val % modulus ∈ residues := by
    simp [residues]
  have hallResidue : ∀ point ∈ head :: tail,
      point.val % modulus ∈ residues := by
    intro point hpoint
    dsimp only [residues]
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨point, hpoint, rfl⟩
  rcases residues with _ | ⟨first, rest⟩
  · simp at hhead
  · rcases rest with _ | ⟨second, rest⟩
    · let shiftedFirst := translatedResidueV89 modulus (-head) first
      have hshiftedFirst : shiftedFirst < modulus :=
        Nat.mod_lt _ (supported_modulus_pos_v89 divisor hdivisor)
      refine ⟨[shiftedFirst], ?_, ?_⟩
      · exact normalizedProjectiveClassSelectionsV88_singleton_mem_v89
          divisor shiftedFirst (by simpa only [modulus] using hshiftedFirst)
      · intro point hpoint
        have hresidue : point.val % modulus = first := by
          have : point.val % modulus ∈ [first] :=
            hallResidue point hpoint
          simpa using this
        change translatedResidueV89 modulus (-head)
            (point.val % modulus) ∈ [shiftedFirst]
        simp [shiftedFirst, hresidue]
    · have hrest : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hlength
        omega
      let shiftedFirst := translatedResidueV89 modulus (-head) first
      let shiftedSecond := translatedResidueV89 modulus (-head) second
      have hshiftedFirst : shiftedFirst < modulus :=
        Nat.mod_lt _ (supported_modulus_pos_v89 divisor hdivisor)
      have hshiftedSecond : shiftedSecond < modulus :=
        Nat.mod_lt _ (supported_modulus_pos_v89 divisor hdivisor)
      refine ⟨[shiftedFirst, shiftedSecond], ?_, ?_⟩
      · exact normalizedProjectiveClassSelectionsV88_pair_mem_v89
          divisor shiftedFirst shiftedSecond
          (by simpa only [modulus] using hshiftedFirst)
          (by simpa only [modulus] using hshiftedSecond)
      · intro point hpoint
        have hresidue :
            point.val % modulus = first ∨
              point.val % modulus = second := by
          have : point.val % modulus ∈ first :: second :: rest :=
            hallResidue point hpoint
          simpa [hrest] using this
        rcases hresidue with hfirst | hsecond
        · change translatedResidueV89 modulus (-head)
              (point.val % modulus) ∈ [shiftedFirst, shiftedSecond]
          simp [shiftedFirst, hfirst]
        · change translatedResidueV89 modulus (-head)
              (point.val % modulus) ∈ [shiftedFirst, shiftedSecond]
          simp [shiftedSecond, hsecond]

private theorem affineSet_subset_classDomain_v89
    (divisor : Nat)
    (hdivisor : divisor = 3 ∨ divisor = 4 ∨ divisor = 6)
    (shift : RawPoint) (set : RawSet) (selection : List Nat)
    (hselection : ∀ point ∈ set,
      translatedResidueV89 (36 / divisor) shift
          (point.val % (36 / divisor)) ∈ selection) :
    ∀ point ∈ affineSet 1 shift set,
      point ∈ normalizedProjectiveClassDomainV88 divisor selection := by
  intro point hpoint
  rcases List.mem_map.mp hpoint with ⟨source, hsource, rfl⟩
  rw [normalizedProjectiveClassDomainV88, List.mem_filter]
  refine ⟨by simp [rawUniverse], ?_⟩
  apply List.any_eq_true.mpr
  let residue := translatedResidueV89 (36 / divisor) shift
    (source.val % (36 / divisor))
  refine ⟨residue, hselection source hsource, ?_⟩
  exact beq_iff_eq.mpr (affinePoint_mod_of_dvd_v89
    (36 / divisor)
    (supported_modulus_dvd_thirtySix_v89 divisor hdivisor) shift source)

structure NormalizedProjectiveFormV89 (U V : RawSet) where
  divisor : Nat
  supported : divisor = 3 ∨ divisor = 4 ∨ divisor = 6
  normalizedU : RawSet
  normalizedV : RawSet
  normalizedU_mem : normalizedU ∈ normalizedProjectiveUChoicesV88 divisor
  normalizedV_mem : normalizedV ∈ normalizedProjectiveVChoicesV88 divisor
  normalizedU_valid : validSixSetB normalizedU = true
  normalizedV_valid : validSixSetB normalizedV = true
  uShift : RawPoint
  vShift : RawPoint
  uPerm : U.Perm (affineSet 1 uShift normalizedU)
  vPerm : V.Perm (affineSet 1 vShift normalizedV)

private theorem normalize_two_class_side_v89
    (divisor : Nat)
    (hdivisor : divisor = 3 ∨ divisor = 4 ∨ divisor = 6)
    (head : RawPoint) (tail : List RawPoint)
    (hvalid : validSixSetB (head :: tail) = true)
    (hclasses : classCount (head :: tail) (36 / divisor) ≤ 2) :
    ∃ normalizedU ∈ normalizedProjectiveUChoicesV88 divisor,
      validSixSetB normalizedU = true ∧
      (head :: tail).Perm (affineSet 1 head normalizedU) := by
  rcases exists_translated_class_selection_v89
      divisor hdivisor head tail hclasses with
    ⟨selection, hselection, hall⟩
  let translated := affineSet 1 (-head) (head :: tail)
  let domain := normalizedProjectiveClassDomainV88 divisor selection
  let normalized := canonicalWithinV89 domain translated
  have hsubset : ∀ point ∈ translated, point ∈ domain := by
    exact affineSet_subset_classDomain_v89
      divisor hdivisor (-head) (head :: tail) selection hall
  have htranslatedValid : validSixSetB translated = true :=
    (validSixSetB_affineSet_iff_v89 (-head) (head :: tail)).2 hvalid
  have hperm : normalized.Perm translated :=
    canonicalWithinV89_perm domain translated
      (normalizedProjectiveClassDomainV88_nodup_v89 divisor selection)
      (validSixSetB_nodup_v88 htranslatedValid) hsubset
  have hlength : normalized.length = 6 := by
    rw [hperm.length_eq]
    exact validSixSetB_length_v88 htranslatedValid
  have hnodup : normalized.Nodup :=
    (normalizedProjectiveClassDomainV88_nodup_v89
      divisor selection).sublist (canonicalWithinV89_sublist domain translated)
  have hzeroTranslated : 0 ∈ translated := by
    exact mem_affineSet_neg_head_v89 head tail
  have hzero : 0 ∈ normalized :=
    (canonicalWithinV89_mem_iff domain translated hsubset 0).2
      hzeroTranslated
  have hchoiceForSelection :
      normalized ∈ normalizedProjectiveUChoicesForSelectionV88
        divisor selection := by
    rw [normalizedProjectiveUChoicesForSelectionV88, List.mem_filter]
    exact ⟨List.mem_sublistsLen.mpr
      ⟨canonicalWithinV89_sublist domain translated, hlength⟩,
      decide_eq_true hzero⟩
  have hchoice : normalized ∈ normalizedProjectiveUChoicesV88 divisor := by
    rw [normalizedProjectiveUChoicesV88]
    exact List.mem_flatMap.mpr
      ⟨selection, hselection, hchoiceForSelection⟩
  exact ⟨normalized, hchoice,
    validSixSetB_of_length_nodup_v89 hlength hnodup,
    affineSet_perm_inverse_v89 head (head :: tail) normalized hperm⟩

private theorem normalize_projective_side_v89
    (head : RawPoint) (tail : List RawPoint)
    (hvalid : validSixSetB (head :: tail) = true) :
    let divisor := differenceGcd (head :: tail)
    ∃ normalizedV ∈ normalizedProjectiveVChoicesV88 divisor,
      validSixSetB normalizedV = true ∧
      (head :: tail).Perm (affineSet 1 head normalizedV) := by
  let divisor := differenceGcd (head :: tail)
  let translated := affineSet 1 (-head) (head :: tail)
  let domain := baseForDivisor divisor
  let normalized := canonicalWithinV89 domain translated
  have hdvd : divisor ∣ 36 := differenceGcd_dvd_thirtySix_v88 _
  have hsubset : ∀ point ∈ translated, point ∈ domain := by
    intro point hpoint
    rcases List.mem_map.mp hpoint with ⟨source, hsource, rfl⟩
    change affinePoint 1 (-head) source ∈
      rawUniverse.filter fun point => point.val % divisor == 0
    rw [List.mem_filter]
    refine ⟨by simp [rawUniverse], ?_⟩
    have hsourceMod : source.val % divisor = head.val % divisor :=
      modEq_of_dvd_natAbsDiff_v88 divisor source.val head.val
        (differenceGcd_dvd_natAbsDiff_v88 head tail hsource)
    rw [affinePoint_mod_of_dvd_v89 divisor hdvd, hsourceMod]
    rw [← affinePoint_mod_of_dvd_v89 divisor hdvd]
    simp
  have htranslatedValid : validSixSetB translated = true :=
    (validSixSetB_affineSet_iff_v89 (-head) (head :: tail)).2 hvalid
  have hperm : normalized.Perm translated :=
    canonicalWithinV89_perm domain translated
      (baseForDivisor_nodup_v89 divisor)
      (validSixSetB_nodup_v88 htranslatedValid) hsubset
  have hlength : normalized.length = 6 := by
    rw [hperm.length_eq]
    exact validSixSetB_length_v88 htranslatedValid
  have hnodup : normalized.Nodup :=
    (baseForDivisor_nodup_v89 divisor).sublist
      (canonicalWithinV89_sublist domain translated)
  have hzero : 0 ∈ normalized :=
    (canonicalWithinV89_mem_iff domain translated hsubset 0).2
      (mem_affineSet_neg_head_v89 head tail)
  have hchoice : normalized ∈ normalizedProjectiveVChoicesV88 divisor := by
    rw [normalizedProjectiveVChoicesV88, List.mem_filter]
    exact ⟨List.mem_sublistsLen.mpr
      ⟨canonicalWithinV89_sublist domain translated, hlength⟩,
      decide_eq_true hzero⟩
  exact ⟨normalized, hchoice,
    validSixSetB_of_length_nodup_v89 hlength hnodup,
    affineSet_perm_inverse_v89 head (head :: tail) normalized hperm⟩

theorem exists_normalizedProjectiveFormV89
    (U V : RawSet)
    (hvalidU : validSixSetB U = true)
    (hvalidV : validSixSetB V = true)
    (hclasses : classCount U (36 / differenceGcd V) ≤ 2) :
    Nonempty (NormalizedProjectiveFormV89 U V) := by
  rcases U with _ | ⟨uHead, uTail⟩
  · simp [validSixSetB] at hvalidU
  rcases V with _ | ⟨vHead, vTail⟩
  · simp [validSixSetB] at hvalidV
  let divisor := differenceGcd (vHead :: vTail)
  have hsupported : divisor = 3 ∨ divisor = 4 ∨ divisor = 6 :=
    supported_differenceGcd_of_valid_classCount_v88
      (uHead :: uTail) (vHead :: vTail) hvalidU hvalidV hclasses
  rcases normalize_two_class_side_v89 divisor hsupported
      uHead uTail hvalidU hclasses with
    ⟨normalizedU, hnormalizedU, hnormalizedUValid, huPerm⟩
  rcases normalize_projective_side_v89 vHead vTail hvalidV with
    ⟨normalizedV, hnormalizedV, hnormalizedVValid, hvPerm⟩
  exact ⟨{
    divisor := divisor
    supported := hsupported
    normalizedU := normalizedU
    normalizedV := normalizedV
    normalizedU_mem := hnormalizedU
    normalizedV_mem := by simpa only [divisor] using hnormalizedV
    normalizedU_valid := hnormalizedUValid
    normalizedV_valid := hnormalizedVValid
    uShift := uHead
    vShift := vHead
    uPerm := huPerm
    vPerm := hvPerm
  }⟩

#print axioms exists_normalizedProjectiveFormV89

end Fuglede.Z180K30ExceptionalRawV2
