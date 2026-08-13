import Fuglede.Z180K30ExceptionalProjectiveTraceTransportV88
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Divisor reduction for a normalized K30 projective pair

For a valid six-set `V`, `differenceGcd V` is a positive divisor of 36.
If a second valid six-set occupies at most two classes modulo
`36 / differenceGcd V`, cardinality eliminates gcds 1 and 2; cardinality of
the single congruence class containing `V` eliminates gcds above 6.  Thus the
only cases are 3, 4 and 6.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem foldl_gcd_dvd_initial_v88
    (values : List Nat) (initial : Nat) :
    values.foldl Nat.gcd initial ∣ initial := by
  induction values generalizing initial with
  | nil => simp
  | cons value values ih =>
      simp only [List.foldl_cons]
      exact (ih (Nat.gcd initial value)).trans
        (Nat.gcd_dvd_left initial value)

theorem differenceGcd_dvd_thirtySix_v88 (set : RawSet) :
    differenceGcd set ∣ 36 := by
  cases set with
  | nil => simp [differenceGcd]
  | cons head tail =>
      rw [differenceGcd, ← List.foldl_map]
      exact
        foldl_gcd_dvd_initial_v88
          (tail.map fun point => natAbsDiff point.val head.val) 36

private theorem foldl_gcd_dvd_of_mem_v88
    (values : List Nat) (initial value : Nat)
    (hvalue : value ∈ values) :
    values.foldl Nat.gcd initial ∣ value := by
  induction values generalizing initial with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact (foldl_gcd_dvd_initial_v88 tail _).trans
          (Nat.gcd_dvd_right initial value)
      · exact ih (Nat.gcd initial head) htail

theorem differenceGcd_dvd_natAbsDiff_v88
    (head : RawPoint) (tail : List RawPoint)
    {point : RawPoint} (hpoint : point ∈ head :: tail) :
    differenceGcd (head :: tail) ∣ natAbsDiff point.val head.val := by
  rcases List.mem_cons.mp hpoint with rfl | htail
  · simp [natAbsDiff]
  · rw [differenceGcd, ← List.foldl_map]
    exact
      foldl_gcd_dvd_of_mem_v88
        (tail.map fun candidate => natAbsDiff candidate.val head.val)
        36 (natAbsDiff point.val head.val) (List.mem_map.mpr ⟨point, htail, rfl⟩)

theorem modEq_of_dvd_natAbsDiff_v88
    (modulus left right : Nat)
    (hdvd : modulus ∣ natAbsDiff left right) :
    left ≡ right [MOD modulus] := by
  by_cases hle : left ≤ right
  · rw [natAbsDiff, if_pos hle] at hdvd
    exact (Nat.modEq_iff_dvd' hle).mpr hdvd
  · have hright : right ≤ left := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rw [natAbsDiff, if_neg hle] at hdvd
    exact ((Nat.modEq_iff_dvd' hright).mpr hdvd).symm

private theorem eraseDups_eq_self_of_nodup_v88 :
    ∀ set : List Nat, set.Nodup → set.eraseDups = set
  | [], _ => by simp
  | head :: tail, hnodup => by
      rw [List.eraseDups_cons]
      have hfiltered : tail.filter (fun point => !point == head) = tail := by
        apply List.filter_eq_self.mpr
        intro point hpoint
        have hne : point ≠ head :=
          fun heq => hnodup.notMem (heq ▸ hpoint)
        simp [hne]
      rw [hfiltered, eraseDups_eq_self_of_nodup_v88 tail hnodup.tail]

private theorem classCount_ge_three_mod_thirtySix_v88
    (set : RawSet) (hvalid : validSixSetB set = true) :
    3 ≤ classCount set 36 := by
  have hnodup := validSixSetB_nodup_v88 hvalid
  have hmapped :
      (set.map fun point => point.val % 36).Nodup := by
    apply hnodup.map
    intro left right heq
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt left.isLt,
      Nat.mod_eq_of_lt right.isLt] using heq
  rw [classCount]
  have herase :
      (set.map fun point => point.val % 36).eraseDups =
        (set.map fun point => point.val % 36) := by
    exact eraseDups_eq_self_of_nodup_v88 _ hmapped
  rw [herase]
  simpa only [List.length_map] using
    (show 3 ≤ set.length by
      rw [validSixSetB_length_v88 hvalid]
      norm_num)

private theorem classCount_ge_three_mod_eighteen_v88
    (set : RawSet) (hvalid : validSixSetB set = true) :
    3 ≤ classCount set 18 := by
  let residues := (set.map fun point => point.val % 18).eraseDups
  have hresiduesLength : residues.length = classCount set 18 := by
    rfl
  by_contra hnot
  have hle : residues.length ≤ 2 := by omega
  have hall (point : RawPoint) (hpoint : point ∈ set) :
      point.val % 18 ∈ residues := by
    dsimp only [residues]
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨point, hpoint, rfl⟩
  rcases residues with _ | ⟨first, tail⟩
  · have hpoint : set = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro point hpoint
      simpa using hall point hpoint
    rw [hpoint] at hvalid
    simp [validSixSetB] at hvalid
  · rcases tail with _ | ⟨second, tail⟩
    · have hmapAll : ∀ point ∈ set, point.val % 18 = first := by
        intro point hpoint
        simpa using hall point hpoint
      have hfiber : set.toFinset ⊆
          Finset.univ.filter fun point : RawPoint =>
            point.val % 18 = first := by
        intro point hpoint
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hmapAll point (List.mem_toFinset.mp hpoint)
      have hcard : set.toFinset.card = 6 := by
        rw [List.toFinset_card_of_nodup (validSixSetB_nodup_v88 hvalid),
          validSixSetB_length_v88 hvalid]
      have hfiberCard :
          (Finset.univ.filter fun point : RawPoint =>
            point.val % 18 = first).card ≤ 2 := by
        by_cases hfirst : first < 18
        · interval_cases first <;> decide
        · have hempty :
              (Finset.univ.filter fun point : RawPoint =>
                point.val % 18 = first) = ∅ := by
            ext point
            simp
            omega
          simp [hempty]
      have := Finset.card_le_card hfiber
      omega
    · have htailNil : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hresidueLength : (first :: second :: tail).length ≤ 2 := hle
        simp only [List.length_cons, List.length_nil] at hresidueLength
        omega
      have hmapPair : ∀ point ∈ set,
          point.val % 18 = first ∨ point.val % 18 = second := by
        intro point hpoint
        simpa only [htailNil, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] using
          hall point hpoint
      -- Each class modulo 18 contains at most two points; two such classes
      -- therefore contain at most four distinct points, contradicting six.
      have hsetCard : set.toFinset.card = 6 := by
        rw [List.toFinset_card_of_nodup (validSixSetB_nodup_v88 hvalid),
          validSixSetB_length_v88 hvalid]
      let fiber (residue : Nat) : Finset RawPoint :=
        Finset.univ.filter fun point => point.val % 18 = residue
      have hsubset : set.toFinset ⊆ fiber first ∪ fiber second := by
        intro point hpoint
        rcases hmapPair point (List.mem_toFinset.mp hpoint) with h | h
        · exact Finset.mem_union_left _ (by simp [fiber, h])
        · exact Finset.mem_union_right _ (by simp [fiber, h])
      have hfiber (residue : Nat) : (fiber residue).card ≤ 2 := by
        dsimp only [fiber]
        by_cases hresidue : residue < 18
        · interval_cases residue <;> decide
        · have hempty :
              (Finset.univ.filter fun point : RawPoint =>
                point.val % 18 = residue) = ∅ := by
            ext point
            simp
            omega
          simp [hempty]
      have hunion : (fiber first ∪ fiber second).card ≤ 4 := by
        have hfirst := hfiber first
        have hsecond := hfiber second
        exact (Finset.card_union_le _ _).trans (by omega)
      have := (Finset.card_le_card hsubset).trans hunion
      omega

private theorem modFiber9_card_lt_six_v88 (residue : RawPoint) :
    (Finset.univ.filter fun point : RawPoint =>
      point.val % 9 = residue.val % 9).card < 6 := by
  fin_cases residue <;> decide

private theorem modFiber12_card_lt_six_v88 (residue : RawPoint) :
    (Finset.univ.filter fun point : RawPoint =>
      point.val % 12 = residue.val % 12).card < 6 := by
  fin_cases residue <;> decide

private theorem modFiber18_card_lt_six_v88 (residue : RawPoint) :
    (Finset.univ.filter fun point : RawPoint =>
      point.val % 18 = residue.val % 18).card < 6 := by
  fin_cases residue <;> decide

private theorem modFiber36_card_lt_six_v88 (residue : RawPoint) :
    (Finset.univ.filter fun point : RawPoint =>
      point.val % 36 = residue.val % 36).card < 6 := by
  fin_cases residue <;> decide

private theorem differenceGcd_le_six_of_valid_v88
    (set : RawSet) (hvalid : validSixSetB set = true) :
    differenceGcd set ≤ 6 := by
  rcases set with _ | ⟨head, tail⟩
  · simp [validSixSetB] at hvalid
  let d := differenceGcd (head :: tail)
  have hdvd : d ∣ 36 := differenceGcd_dvd_thirtySix_v88 _
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hdle : d ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd
  have hcard : (head :: tail).toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup (validSixSetB_nodup_v88 hvalid),
      validSixSetB_length_v88 hvalid]
  have hmod (point : RawPoint) (hpoint : point ∈ head :: tail) :
      point.val % d = head.val % d :=
    modEq_of_dvd_natAbsDiff_v88 d point.val head.val
      (differenceGcd_dvd_natAbsDiff_v88 head tail hpoint)
  have hfiberSubset (modulus : Nat) (hd : d = modulus) :
      (head :: tail).toFinset ⊆
        Finset.univ.filter fun point : RawPoint =>
          point.val % modulus = head.val % modulus := by
    intro point hpoint
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hd] using hmod point (List.mem_toFinset.mp hpoint)
  by_contra hnot
  have hdseven : 7 ≤ d := by omega
  have hcases : d = 9 ∨ d = 12 ∨ d = 18 ∨ d = 36 := by
    interval_cases d <;> norm_num at hdvd
    all_goals simp
  rcases hcases with h9 | h12 | h18 | h36
  · have := Finset.card_le_card (hfiberSubset 9 h9)
    rw [hcard] at this
    exact (Nat.not_lt_of_ge this) (modFiber9_card_lt_six_v88 head)
  · have := Finset.card_le_card (hfiberSubset 12 h12)
    rw [hcard] at this
    exact (Nat.not_lt_of_ge this) (modFiber12_card_lt_six_v88 head)
  · have := Finset.card_le_card (hfiberSubset 18 h18)
    rw [hcard] at this
    exact (Nat.not_lt_of_ge this) (modFiber18_card_lt_six_v88 head)
  · have := Finset.card_le_card (hfiberSubset 36 h36)
    rw [hcard] at this
    exact (Nat.not_lt_of_ge this) (modFiber36_card_lt_six_v88 head)

theorem supported_differenceGcd_of_valid_classCount_v88
    (U V : RawSet)
    (hvalidU : validSixSetB U = true)
    (hvalidV : validSixSetB V = true)
    (hclasses : classCount U (36 / differenceGcd V) ≤ 2) :
    differenceGcd V = 3 ∨ differenceGcd V = 4 ∨
      differenceGcd V = 6 := by
  let d := differenceGcd V
  have hdvd : d ∣ 36 := differenceGcd_dvd_thirtySix_v88 V
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hdle : d ≤ 6 := differenceGcd_le_six_of_valid_v88 V hvalidV
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
    interval_cases d <;> norm_num at hdvd
    all_goals simp
  rcases hcases with h1 | h2 | h3 | h4 | h6
  · have hthree := classCount_ge_three_mod_thirtySix_v88 U hvalidU
    have hclasses' : classCount U 36 ≤ 2 := by
      simpa only [d, h1] using hclasses
    omega
  · have hthree := classCount_ge_three_mod_eighteen_v88 U hvalidU
    have hclasses' : classCount U 18 ≤ 2 := by
      simpa only [d, h2] using hclasses
    omega
  · exact Or.inl (by simpa only [d] using h3)
  · exact Or.inr (Or.inl (by simpa only [d] using h4))
  · exact Or.inr (Or.inr (by simpa only [d] using h6))

#print axioms supported_differenceGcd_of_valid_classCount_v88

end Fuglede.Z180K30ExceptionalRawV2
