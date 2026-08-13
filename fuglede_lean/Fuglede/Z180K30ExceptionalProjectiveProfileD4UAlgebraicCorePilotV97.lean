import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UBase
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-! Generic core for the bounded structural D4-U completeness bridge. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (domain : List alpha) (length : Nat)
    (hpoint : point ∉ domain) :
    (List.sublistsLen length domain).filter
      (fun values => decide (point ∈ values)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro values hvalues hcontains
  have hmember : point ∈ values := of_decide_eq_true hcontains
  have hsublist := (List.mem_sublistsLen.mp hvalues).1
  exact hpoint (hsublist.subset hmember)

theorem z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) = values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true List.mem_cons_self

def z180K30ProjectiveD4UCombPilotV97
    (frame domain : RawSet) (length : Nat) : List RawSet :=
  (List.sublistsLen length domain).map fun suffix => frame ++ suffix

theorem z180_k30_projective_d4_u_comb_succ_cons_pilot_v97
    (frame : RawSet) (head : RawPoint) (tail : RawSet) (length : Nat) :
    z180K30ProjectiveD4UCombPilotV97 frame (head :: tail) (length + 1) =
      z180K30ProjectiveD4UCombPilotV97 frame tail (length + 1) ++
        z180K30ProjectiveD4UCombPilotV97 (frame ++ [head]) tail length := by
  simp only [z180K30ProjectiveD4UCombPilotV97,
    List.sublistsLen_succ_cons, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro suffix _
  change frame ++ head :: suffix = frame ++ [head] ++ suffix
  rw [List.append_assoc, List.singleton_append]

def z180K30ProjectiveD4UCombChunksPilotV97 :
    Nat → RawSet → RawSet → Nat → List (List RawSet)
  | 0, frame, domain, length =>
      [z180K30ProjectiveD4UCombPilotV97 frame domain length]
  | _ + 1, frame, domain, 0 =>
      [z180K30ProjectiveD4UCombPilotV97 frame domain 0]
  | _ + 1, frame, [], length + 1 =>
      [z180K30ProjectiveD4UCombPilotV97 frame [] (length + 1)]
  | fuel + 1, frame, head :: tail, length + 1 =>
      z180K30ProjectiveD4UCombChunksPilotV97 fuel frame tail (length + 1) ++
        z180K30ProjectiveD4UCombChunksPilotV97
          fuel (frame ++ [head]) tail length

theorem z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97 :
    ∀ fuel frame domain length,
      (z180K30ProjectiveD4UCombChunksPilotV97
        fuel frame domain length).flatten =
        z180K30ProjectiveD4UCombPilotV97 frame domain length
  | 0, frame, domain, length => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | _ + 1, frame, domain, 0 => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | fuel + 1, frame, [], length + 1 => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | fuel + 1, frame, head :: tail, length + 1 => by
      rw [z180K30ProjectiveD4UCombChunksPilotV97, List.flatten_append,
        z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d4_u_comb_succ_cons_pilot_v97]

def z180K30ProjectiveD4UTailR01PilotV97 : RawSet := [1, 9, 10, 18, 19, 27, 28]
def z180K30ProjectiveD4UBlockR01PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR01PilotV97 5
def z180K30ProjectiveD4UTailR02PilotV97 : RawSet := [2, 9, 11, 18, 20, 27, 29]
def z180K30ProjectiveD4UBlockR02PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR02PilotV97 5
def z180K30ProjectiveD4UTailR03PilotV97 : RawSet := [3, 9, 12, 18, 21, 27, 30]
def z180K30ProjectiveD4UBlockR03PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR03PilotV97 5
def z180K30ProjectiveD4UTailR04PilotV97 : RawSet := [4, 9, 13, 18, 22, 27, 31]
def z180K30ProjectiveD4UBlockR04PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR04PilotV97 5
def z180K30ProjectiveD4UTailR05PilotV97 : RawSet := [5, 9, 14, 18, 23, 27, 32]
def z180K30ProjectiveD4UBlockR05PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR05PilotV97 5
def z180K30ProjectiveD4UTailR06PilotV97 : RawSet := [6, 9, 15, 18, 24, 27, 33]
def z180K30ProjectiveD4UBlockR06PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR06PilotV97 5
def z180K30ProjectiveD4UTailR07PilotV97 : RawSet := [7, 9, 16, 18, 25, 27, 34]
def z180K30ProjectiveD4UBlockR07PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR07PilotV97 5
def z180K30ProjectiveD4UTailR08PilotV97 : RawSet := [8, 9, 17, 18, 26, 27, 35]
def z180K30ProjectiveD4UBlockR08PilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97 [0] z180K30ProjectiveD4UTailR08PilotV97 5

def z180K30ProjectiveD4UCanonicalPilotV97 : List RawSet :=
  z180K30ProjectiveD4UBlockR01PilotV97 ++
    z180K30ProjectiveD4UBlockR02PilotV97 ++
    z180K30ProjectiveD4UBlockR03PilotV97 ++
    z180K30ProjectiveD4UBlockR04PilotV97 ++
    z180K30ProjectiveD4UBlockR05PilotV97 ++
    z180K30ProjectiveD4UBlockR06PilotV97 ++
    z180K30ProjectiveD4UBlockR07PilotV97 ++
    z180K30ProjectiveD4UBlockR08PilotV97

def z180K30ProjectiveD4UCanonicalIndicesPilotV97 : List Nat :=
  [11, 80, 10, 79, 9, 78, 8, 77, 7, 76, 6, 5, 75, 4, 74, 3, 73, 2, 1, 72, 0, 23, 89, 22, 88, 21, 87, 20, 86, 19, 85, 18, 17, 84, 16, 83, 15, 82, 14, 13, 81, 12, 137, 158, 136, 157, 135, 156, 134, 155, 133, 154, 132, 131, 153, 130, 152, 129, 151, 128, 127, 150, 126, 35, 98, 34, 97, 33, 96, 32, 95, 31, 94, 30, 29, 93, 28, 92, 27, 91, 26, 25, 90, 24, 47, 107, 46, 106, 45, 105, 44, 104, 43, 103, 42, 41, 102, 40, 101, 39, 100, 38, 37, 99, 36, 149, 167, 148, 166, 147, 165, 146, 164, 145, 163, 144, 143, 162, 142, 161, 141, 160, 140, 139, 159, 138, 59, 116, 58, 115, 57, 114, 56, 113, 55, 112, 54, 53, 111, 52, 110, 51, 109, 50, 49, 108, 48, 71, 125, 70, 124, 69, 123, 68, 122, 67, 121, 66, 65, 120, 64, 119, 63, 118, 62, 61, 117, 60]

def z180K30ProjectiveD4UIndexPredicatePilotV97
    (bucket value : Nat) : Bool := value % 17 == bucket

def z180K30ProjectiveD4USourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D4USourceGrouped.getD index []

def z180K30ProjectiveD4UCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCanonicalIndicesPilotV97.map
    z180K30ProjectiveD4USourceAtPilotV97

def z180K30ProjectiveD4USelectionsLiteralPilotV97 : List (List Nat) :=
  [[0], [1], [2], [3], [4], [5], [6], [7], [8], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8], [1, 0], [1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 0], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [2, 7], [2, 8], [3, 0], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5], [3, 6], [3, 7], [3, 8], [4, 0], [4, 1], [4, 2], [4, 3], [4, 4], [4, 5], [4, 6], [4, 7], [4, 8], [5, 0], [5, 1], [5, 2], [5, 3], [5, 4], [5, 5], [5, 6], [5, 7], [5, 8], [6, 0], [6, 1], [6, 2], [6, 3], [6, 4], [6, 5], [6, 6], [6, 7], [6, 8], [7, 0], [7, 1], [7, 2], [7, 3], [7, 4], [7, 5], [7, 6], [7, 7], [7, 8], [8, 0], [8, 1], [8, 2], [8, 3], [8, 4], [8, 5], [8, 6], [8, 7], [8, 8]]

theorem z180_k30_projective_d4_u_selections_literal_pilot_v97 :
    normalizedProjectiveClassSelectionsV88 4 =
      z180K30ProjectiveD4USelectionsLiteralPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
