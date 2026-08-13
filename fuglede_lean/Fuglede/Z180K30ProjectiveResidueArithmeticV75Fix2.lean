import Fuglede.Z180K30FourierProjectiveV74Fix
import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Residue arithmetic for the K30 projective reduction (V75 Fix2)

This clean replacement for the failed V75 variants turns the projective
proportionality congruences of V74 into the two-residue-class predicate used
by the exact raw certificate.  The six-entry `eraseDups` bound is proved by
expanding the core implementation and auditing the two possible values.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

def z36RawPointV75Fix2 (x : ZMod 36) : RawPoint :=
  ⟨x.val, ZMod.val_lt x⟩

@[simp]
theorem z36RawPointV75Fix2_val (x : ZMod 36) :
    (z36RawPointV75Fix2 x).val = x.val := rfl

def z36RawSetV75Fix2 (X : Fin 6 → ZMod 36) : RawSet :=
  List.ofFn fun i => z36RawPointV75Fix2 (X i)

@[simp]
theorem z36RawPointV75Fix2_natCast_rawPoint (x : RawPoint) :
    z36RawPointV75Fix2 (x.val : ZMod 36) = x := by
  apply Fin.ext
  simp [z36RawPointV75Fix2, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]

@[simp]
theorem z36RawSetV75Fix2_natCast_rawPoints (X : Fin 6 → RawPoint) :
    z36RawSetV75Fix2 (fun i => (X i).val : Fin 6 → ZMod 36) =
      List.ofFn X := by
  simp [z36RawSetV75Fix2]

theorem z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix2
    (k x y : ZMod 36)
    (hzero :
      (k.val : ZMod 36) *
          ((x.val : ZMod 36) - (y.val : ZMod 36)) = 0) :
    36 ∣ k.val * natAbsDiff x.val y.val := by
  have hcast :
      ((k.val * natAbsDiff x.val y.val : Nat) : ZMod 36) = 0 := by
    by_cases hxy : x.val ≤ y.val
    · rw [natAbsDiff, if_pos hxy, Nat.cast_mul, Nat.cast_sub hxy]
      calc
        (k.val : ZMod 36) *
              ((y.val : ZMod 36) - (x.val : ZMod 36)) =
            -((k.val : ZMod 36) *
              ((x.val : ZMod 36) - (y.val : ZMod 36))) := by ring
        _ = 0 := by rw [hzero]; simp
    · have hyx : y.val ≤ x.val := Nat.le_of_not_ge hxy
      rw [natAbsDiff, if_neg hxy, Nat.cast_mul, Nat.cast_sub hyx]
      exact hzero
  exact (ZMod.natCast_eq_zero_iff
    (k.val * natAbsDiff x.val y.val) 36).mp hcast

private theorem thirtySix_dvd_mul_foldl_point_gcd_v75Fix2
    (k initial : Nat) (head : RawPoint) (tail : List RawPoint)
    (hinitial : 36 ∣ k * initial)
    (htail : ∀ point ∈ tail,
      36 ∣ k * natAbsDiff point.val head.val) :
    36 ∣ k *
      tail.foldl
        (fun result point =>
          Nat.gcd result (natAbsDiff point.val head.val))
        initial := by
  induction tail generalizing initial with
  | nil => simpa using hinitial
  | cons point tail ih =>
      simp only [List.foldl_cons]
      apply ih
      · rw [← Nat.gcd_mul_left]
        exact Nat.dvd_gcd hinitial (htail point (by simp))
      · intro other hother
        exact htail other (by simp [hother])

theorem thirtySix_dvd_mul_differenceGcd_cons_v75Fix2
    (k : Nat) (head : RawPoint) (tail : List RawPoint)
    (htail : ∀ point ∈ tail,
      36 ∣ k * natAbsDiff point.val head.val) :
    36 ∣ k * differenceGcd (head :: tail) := by
  rw [differenceGcd]
  apply thirtySix_dvd_mul_foldl_point_gcd_v75Fix2
  · exact ⟨k, by omega⟩
  · exact htail

private theorem foldl_point_gcd_dvd_initial_v75Fix2
    (head : RawPoint) (tail : List RawPoint) (initial : Nat) :
    tail.foldl
        (fun result point =>
          Nat.gcd result (natAbsDiff point.val head.val))
        initial ∣ initial := by
  induction tail generalizing initial with
  | nil => simp
  | cons point tail ih =>
      simp only [List.foldl_cons]
      exact (ih (Nat.gcd initial
        (natAbsDiff point.val head.val))).trans
          (Nat.gcd_dvd_left initial
            (natAbsDiff point.val head.val))

theorem differenceGcd_dvd_thirtySix_v75Fix2 (set : RawSet) :
    differenceGcd set ∣ 36 := by
  cases set with
  | nil => simp [differenceGcd]
  | cons head tail =>
      simpa only [differenceGcd] using
        foldl_point_gcd_dvd_initial_v75Fix2 head tail 36

theorem thirtySix_div_g_dvd_of_dvd_mul_v75Fix2
    (g k : Nat) (hg : g ∣ 36) (hgpos : 0 < g)
    (hmul : 36 ∣ k * g) :
    36 / g ∣ k := by
  have hgle : g ≤ 36 := Nat.le_of_dvd (by norm_num) hg
  rcases hg with ⟨c, hc⟩
  rcases hmul with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  interval_cases g <;> omega

theorem z36_val_mod_eq_of_dvd_sub_val_v75Fix2
    (d : Nat) (hd : d ∣ 36) (x y : ZMod 36)
    (hsub : d ∣ (x - y).val) :
    x.val % d = y.val % d := by
  let castD : ZMod 36 →+* ZMod d := ZMod.castHom hd (ZMod d)
  have hcastD (z : ZMod 36) :
      castD z = (z.val : ZMod d) := by
    calc
      castD z = castD (z.val : ZMod 36) :=
        congrArg castD (ZMod.natCast_zmod_val z).symm
      _ = (z.val : ZMod d) := by rw [map_natCast]
  have hsubzero : ((x - y).val : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff (x - y).val d).2 hsub
  have hmapped : castD (x - y) = 0 := by
    calc
      castD (x - y) = castD ((x - y).val : ZMod 36) :=
        congrArg castD (ZMod.natCast_zmod_val (x - y)).symm
      _ = ((x - y).val : ZMod d) := by rw [map_natCast]
      _ = 0 := hsubzero
  have hxy : (x.val : ZMod d) = (y.val : ZMod d) := by
    rw [map_sub, hcastD x, hcastD y] at hmapped
    exact sub_eq_zero.mp hmapped
  exact (ZMod.natCast_eq_natCast_iff' x.val y.val d).mp hxy

theorem z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
    (x y : ZMod 36) (V : Fin 6 → ZMod 36)
    (hzero : ∀ l, (x - y) * (V l - V 0) = 0) :
    x.val % (36 / differenceGcd (z36RawSetV75Fix2 V)) =
      y.val % (36 / differenceGcd (z36RawSetV75Fix2 V)) := by
  let g := differenceGcd (z36RawSetV75Fix2 V)
  have hfold : 36 ∣ (x - y).val * g := by
    dsimp only [g]
    rw [z36RawSetV75Fix2, List.ofFn_succ]
    apply thirtySix_dvd_mul_differenceGcd_cons_v75Fix2
    rw [List.forall_mem_ofFn_iff]
    intro i
    have hzmod :
        (((x - y).val : ZMod 36) *
          (((V i.succ).val : ZMod 36) -
            ((V 0).val : ZMod 36))) = 0 := by
      simpa only [ZMod.natCast_zmod_val] using hzero i.succ
    simpa only [z36RawPointV75Fix2_val] using
      z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix2
        (x - y) (V i.succ) (V 0) hzmod
  have hg : g ∣ 36 := differenceGcd_dvd_thirtySix_v75Fix2 _
  have hgpos : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hgzero
    rw [hgzero] at hg
    norm_num at hg
  have hquot : 36 / g ∣ (x - y).val :=
    thirtySix_div_g_dvd_of_dvd_mul_v75Fix2
      g (x - y).val hg hgpos hfold
  have hquot36 : 36 / g ∣ 36 := by
    exact ⟨g, (Nat.div_mul_cancel hg).symm⟩
  exact z36_val_mod_eq_of_dvd_sub_val_v75Fix2
    (36 / g) hquot36 x y hquot

private theorem six_eraseDups_length_le_two_v75Fix2
    (a0 a1 a2 a3 a4 a5 b c : Nat)
    (h0 : a0 = b ∨ a0 = c)
    (h1 : a1 = b ∨ a1 = c)
    (h2 : a2 = b ∨ a2 = c)
    (h3 : a3 = b ∨ a3 = c)
    (h4 : a4 = b ∨ a4 = c)
    (h5 : a5 = b ∨ a5 = c) :
    [a0, a1, a2, a3, a4, a5].eraseDups.length ≤ 2 := by
  by_cases hbc : b = c
  · rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      rcases h5 with h5 | h5 <;>
      simp [h0, h1, h2, h3, h4, h5, hbc,
        List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  · have hbcBool : (b == c) = false := by
      cases h : (b == c) with
      | false => rfl
      | true =>
          exfalso
          exact hbc (LawfulBEq.eq_of_beq h)
    have hcbBool : (c == b) = false := by
      cases h : (c == b) with
      | false => rfl
      | true =>
          exfalso
          exact hbc (LawfulBEq.eq_of_beq h).symm
    rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      rcases h5 with h5 | h5 <;>
      simp [h0, h1, h2, h3, h4, h5, hbcBool, hcbBool,
        List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

theorem classCount_z36RawSetV75Fix2_le_two_of_pair_v75Fix2
    (X : Fin 6 → ZMod 36) (modulus : Nat) (p q : Fin 6)
    (hpair : ∀ i,
      (X i).val % modulus = (X p).val % modulus ∨
        (X i).val % modulus = (X q).val % modulus) :
    classCount (z36RawSetV75Fix2 X) modulus ≤ 2 := by
  change
    [ (X 0).val % modulus, (X 1).val % modulus,
      (X 2).val % modulus, (X 3).val % modulus,
      (X 4).val % modulus, (X 5).val % modulus ].eraseDups.length ≤ 2
  exact six_eraseDups_length_le_two_v75Fix2
    _ _ _ _ _ _ _ _
    (hpair 0) (hpair 1) (hpair 2)
    (hpair 3) (hpair 4) (hpair 5)

theorem z36FourierBlockV74Fix_rows_classCount_le_two_v75Fix2
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hrows : Z180K30RowsCoveredByTwoProjectiveV73Fix
      (z36FourierBlockV74Fix U V) p q) :
    classCount (z36RawSetV75Fix2 U)
      (36 / differenceGcd (z36RawSetV75Fix2 V)) ≤ 2 := by
  apply classCount_z36RawSetV75Fix2_le_two_of_pair_v75Fix2 U _ p q
  intro i
  rcases hrows i with ⟨scale, hrow⟩ | ⟨scale, hrow⟩
  · left
    exact z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
      (U i) (U p) V
      (z36FourierBlockV74Fix_row_proportional_zero
        U V i p scale hrow)
  · right
    exact z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
      (U i) (U q) V
      (z36FourierBlockV74Fix_row_proportional_zero
        U V i q scale hrow)

theorem z36FourierBlockV74Fix_columns_classCount_le_two_v75Fix2
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hcolumns : Z180K30ColumnsCoveredByTwoProjectiveV73Fix
      (z36FourierBlockV74Fix U V) p q) :
    classCount (z36RawSetV75Fix2 V)
      (36 / differenceGcd (z36RawSetV75Fix2 U)) ≤ 2 := by
  apply classCount_z36RawSetV75Fix2_le_two_of_pair_v75Fix2 V _ p q
  intro l
  rcases hcolumns l with ⟨scale, hcolumn⟩ | ⟨scale, hcolumn⟩
  · left
    apply z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
      (V l) (V p) U
    intro a
    simpa only [mul_comm] using
      z36FourierBlockV74Fix_column_proportional_zero
        U V l p scale hcolumn a
  · right
    apply z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
      (V l) (V q) U
    intro a
    simpa only [mul_comm] using
      z36FourierBlockV74Fix_column_proportional_zero
        U V l q scale hcolumn a

theorem z36FourierBlockV74Fix_classCount_dichotomy_v75Fix2
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hprojective :
      Z180K30RowsCoveredByTwoProjectiveV73Fix
          (z36FourierBlockV74Fix U V) p q ∨
        ∃ c d : Fin 6,
          Z180K30ColumnsCoveredByTwoProjectiveV73Fix
            (z36FourierBlockV74Fix U V) c d) :
    classCount (z36RawSetV75Fix2 U)
          (36 / differenceGcd (z36RawSetV75Fix2 V)) ≤ 2 ∨
      classCount (z36RawSetV75Fix2 V)
          (36 / differenceGcd (z36RawSetV75Fix2 U)) ≤ 2 := by
  rcases hprojective with hrows | ⟨c, d, hcolumns⟩
  · exact Or.inl
      (z36FourierBlockV74Fix_rows_classCount_le_two_v75Fix2
        U V p q hrows)
  · exact Or.inr
      (z36FourierBlockV74Fix_columns_classCount_le_two_v75Fix2
        U V c d hcolumns)

theorem z36FourierBlockV74Fix_rankTwoProjectiveCoverB_v75Fix2
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hprojective :
      Z180K30RowsCoveredByTwoProjectiveV73Fix
          (z36FourierBlockV74Fix U V) p q ∨
        ∃ c d : Fin 6,
          Z180K30ColumnsCoveredByTwoProjectiveV73Fix
            (z36FourierBlockV74Fix U V) c d) :
    rankTwoProjectiveCoverB
      (z36RawSetV75Fix2 U) (z36RawSetV75Fix2 V) = true := by
  rcases z36FourierBlockV74Fix_classCount_dichotomy_v75Fix2
      U V p q hprojective with hU | hV
  · simp [rankTwoProjectiveCoverB, hU]
  · simp [rankTwoProjectiveCoverB, hV]

theorem z36FourierBlockV74Fix_rankTwoProjectiveCoverB_of_span_two_v75Fix2
    (U V : Fin 6 → ZMod 36)
    (p q : Fin 6) (alpha beta : Fin 6 → Complex)
    (hspan : ∀ i j,
      z36FourierBlockV74Fix U V i j =
        alpha i * z36FourierBlockV74Fix U V p j +
          beta i * z36FourierBlockV74Fix U V q j) :
    rankTwoProjectiveCoverB
      (z36RawSetV75Fix2 U) (z36RawSetV75Fix2 V) = true := by
  apply z36FourierBlockV74Fix_rankTwoProjectiveCoverB_v75Fix2 U V p q
  exact z36FourierBlockV74Fix_projective_dichotomy_of_span_two
    U V p q alpha beta hspan

#print axioms z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix2
#print axioms z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix2
#print axioms z36FourierBlockV74Fix_classCount_dichotomy_v75Fix2
#print axioms z36FourierBlockV74Fix_rankTwoProjectiveCoverB_of_span_two_v75Fix2

end Fuglede
