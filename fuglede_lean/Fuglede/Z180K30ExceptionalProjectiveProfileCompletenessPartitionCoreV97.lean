import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97

/-!
# Direct finite partition replay for V97 profile completeness

This kernel theorem partitions any list into independent hash buckets while
preserving multiplicities. Generated completeness leaves therefore reduce one
direct filter; no leaf evaluates a chain of preceding filters.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem flatMap_singleton_of_mem_nodup_v97
    {ι α : Type*} [BEq ι] [LawfulBEq ι]
    (a : α) {representative : ι} {indices : List ι}
    (hrepresentative : representative ∈ indices) (hnodup : indices.Nodup) :
    indices.flatMap
      (fun index => if representative == index then [a] else []) = [a] := by
  induction indices generalizing representative with
  | nil => simp at hrepresentative
  | cons index indices ih =>
      have hnotMem : index ∉ indices := (List.nodup_cons.mp hnodup).1
      have htailNodup : indices.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hequal : representative = index
      · subst index
        have htail :
            indices.flatMap
              (fun next => if representative == next then [a] else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro next hnext
          have hne : representative ≠ next := by
            intro hequal
            exact hnotMem (hequal.symm ▸ hnext)
          simp [hne]
        simp [htail]
      · have htailMem : representative ∈ indices :=
          (List.mem_cons.mp hrepresentative).resolve_left hequal
        simpa [hequal] using ih htailMem htailNodup

theorem projectiveProfileRangeFlatMapFilterModPermV97
    {α : Type} (key : α → Nat) (bucketCount : Nat)
    (hpositive : 0 < bucketCount) (list : List α) :
    ((List.range bucketCount).flatMap fun bucket =>
      list.filter fun value => key value % bucketCount == bucket).Perm list := by
  induction list with
  | nil => simp
  | cons head tail ih =>
      have hone :
          ((List.range bucketCount).flatMap fun bucket =>
            if key head % bucketCount == bucket then [head] else []) = [head] :=
        flatMap_singleton_of_mem_nodup_v97 head
          (List.mem_range.mpr (Nat.mod_lt _ hpositive)) List.nodup_range
      have hsplit :
          (((List.range bucketCount).flatMap fun bucket =>
              if key head % bucketCount == bucket then [head] else []) ++
            ((List.range bucketCount).flatMap fun bucket =>
              tail.filter fun value => key value % bucketCount == bucket)).Perm
            ((List.range bucketCount).flatMap fun bucket =>
              (head :: tail).filter fun value =>
                key value % bucketCount == bucket) := by
        have hcombined :=
          List.flatMap_append_perm (List.range bucketCount)
            (fun bucket =>
              if key head % bucketCount == bucket then [head] else [])
            (fun bucket =>
              tail.filter fun value => key value % bucketCount == bucket)
        have hflatMap :
            ((List.range bucketCount).flatMap fun bucket =>
              (if key head % bucketCount == bucket then [head] else []) ++
                tail.filter fun value => key value % bucketCount == bucket) =
              ((List.range bucketCount).flatMap fun bucket =>
                (head :: tail).filter fun value =>
                  key value % bucketCount == bucket) := by
          apply List.flatMap_congr
          intro bucket _
          by_cases hequal : key head % bucketCount = bucket <;>
            simp [List.filter_cons, hequal]
        rw [hflatMap] at hcombined
        exact hcombined
      have hstep :
          ((List.range bucketCount).flatMap fun bucket =>
            (head :: tail).filter fun value =>
              key value % bucketCount == bucket).Perm
            (head :: (List.range bucketCount).flatMap fun bucket =>
              tail.filter fun value => key value % bucketCount == bucket) := by
        simpa only [hone, List.singleton_append] using hsplit.symm
      exact hstep.trans (ih.cons head)

end Fuglede.Z180K30ExceptionalRawV2
