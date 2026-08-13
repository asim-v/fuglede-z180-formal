import Fuglede.Z180K30FourierProjectiveV74Fix
import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Residue arithmetic for the K30 projective reduction

This module turns the projective proportionality congruences of V74 into
the two-residue-class predicate used by the exact raw certificate.  The
argument is entirely over `Nat` and `ZMod 36`:

* a zero product in `ZMod 36` gives divisibility by `36` of the product of
  the corresponding natural representatives;
* those divisibilities propagate through the gcd fold defining
  `differenceGcd`;
* the common gcd can be cancelled because it is a positive divisor of 36;
* six residues, each equal to one of two fixed residues, have `classCount`
  at most two.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

/-- The canonical raw representative of a residue modulo 36. -/
def z36RawPointV75Fix (x : ZMod 36) : RawPoint :=
  ⟨x.val, ZMod.val_lt x⟩

@[simp]
theorem z36RawPointV75Fix_val (x : ZMod 36) :
    (z36RawPointV75Fix x).val = x.val := rfl

/-- A six-tuple of residues, viewed in the raw-certificate list format. -/
def z36RawSetV75Fix (X : Fin 6 → ZMod 36) : RawSet :=
  List.ofFn fun i => z36RawPointV75Fix (X i)

@[simp]
theorem z36RawPointV75Fix_natCast_rawPoint (x : RawPoint) :
    z36RawPointV75Fix (x.val : ZMod 36) = x := by
  apply Fin.ext
  simp [z36RawPointV75Fix, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]

@[simp]
theorem z36RawSetV75Fix_natCast_rawPoints (X : Fin 6 → RawPoint) :
    z36RawSetV75Fix (fun i => (X i).val : Fin 6 → ZMod 36) =
      List.ofFn X := by
  simp [z36RawSetV75Fix]

/-- A modular zero product yields ordinary divisibility of the product with
the unsigned difference of the chosen representatives. -/
theorem z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix
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

/-- Divisibility by 36 propagates through the pointwise gcd fold used by
`differenceGcd`. -/
private theorem thirtySix_dvd_mul_foldl_point_gcd_v75Fix
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

/-- The preceding fold lemma at the exact `differenceGcd` definition. -/
theorem thirtySix_dvd_mul_differenceGcd_cons_v75Fix
    (k : Nat) (head : RawPoint) (tail : List RawPoint)
    (htail : ∀ point ∈ tail,
      36 ∣ k * natAbsDiff point.val head.val) :
    36 ∣ k * differenceGcd (head :: tail) := by
  rw [differenceGcd]
  apply thirtySix_dvd_mul_foldl_point_gcd_v75Fix
  · exact ⟨k, by omega⟩
  · exact htail

/-- Every `differenceGcd` is a divisor of 36, since its fold starts at 36. -/
private theorem foldl_point_gcd_dvd_initial_v75Fix
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

theorem differenceGcd_dvd_thirtySix_v75Fix (set : RawSet) :
    differenceGcd set ∣ 36 := by
  cases set with
  | nil => simp [differenceGcd]
  | cons head tail =>
      simpa only [differenceGcd] using
        foldl_point_gcd_dvd_initial_v75Fix head tail 36

/-- Cancellation for the finite list of positive divisors of 36. -/
theorem thirtySix_div_g_dvd_of_dvd_mul_v75Fix
    (g k : Nat) (hg : g ∣ 36) (hgpos : 0 < g)
    (hmul : 36 ∣ k * g) :
    36 / g ∣ k := by
  have hgle : g ≤ 36 := Nat.le_of_dvd (by norm_num) hg
  rcases hg with ⟨c, hc⟩
  rcases hmul with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  interval_cases g <;> omega

/-- Congruence modulo a divisor of 36 can be read from the value of a
subtraction in `ZMod 36`. -/
theorem z36_val_mod_eq_of_dvd_sub_val_v75Fix
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

/-- All Fourier congruences against one six-tuple force equality modulo the
quotient by that tuple's `differenceGcd`. -/
theorem z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
    (x y : ZMod 36) (V : Fin 6 → ZMod 36)
    (hzero : ∀ l, (x - y) * (V l - V 0) = 0) :
    x.val % (36 / differenceGcd (z36RawSetV75Fix V)) =
      y.val % (36 / differenceGcd (z36RawSetV75Fix V)) := by
  let g := differenceGcd (z36RawSetV75Fix V)
  have hfold : 36 ∣ (x - y).val * g := by
    dsimp only [g]
    rw [z36RawSetV75Fix, List.ofFn_succ]
    apply thirtySix_dvd_mul_differenceGcd_cons_v75Fix
    rw [List.forall_mem_ofFn_iff]
    intro i
    have hzmod :
        (((x - y).val : ZMod 36) *
          (((V i.succ).val : ZMod 36) -
            ((V 0).val : ZMod 36))) = 0 := by
      simpa only [ZMod.natCast_zmod_val] using hzero i.succ
    simpa only [z36RawPointV75Fix_val] using
      z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix
        (x - y) (V i.succ) (V 0) hzmod
  have hg : g ∣ 36 := differenceGcd_dvd_thirtySix_v75Fix _
  have hgpos : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hgzero
    rw [hgzero] at hg
    norm_num at hg
  have hquot : 36 / g ∣ (x - y).val :=
    thirtySix_div_g_dvd_of_dvd_mul_v75Fix g (x - y).val hg hgpos hfold
  have hquot36 : 36 / g ∣ 36 := by
    exact ⟨g, (Nat.div_mul_cancel hg).symm⟩
  exact z36_val_mod_eq_of_dvd_sub_val_v75Fix
    (36 / g) hquot36 x y hquot

/-- A duplicate-free list contained in a two-element finset has length at
most two. -/
private theorem eraseDups_length_le_two_of_pair_v75Fix
    (values : List Nat) (first second : Nat)
    (hvalues : ∀ x ∈ values, x = first ∨ x = second) :
    values.eraseDups.length ≤ 2 := by
  have hsubset :
      values.eraseDups.toFinset ⊆
        ({first, second} : Finset Nat) := by
    intro x hx
    have hxvalues : x ∈ values := by
      simpa using hx
    simpa using hvalues x hxvalues
  have hcard := Finset.card_le_card hsubset
  calc
    values.eraseDups.length =
        values.eraseDups.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup List.nodup_eraseDups
    _ ≤ ({first, second} : Finset Nat).card := hcard
    _ ≤ 2 := by simp

/-- A six-element raw list whose residues all equal one of two fixed
residues has at most two distinct residue classes. -/
theorem classCount_z36RawSetV75Fix_le_two_of_pair_v75Fix
    (X : Fin 6 → ZMod 36) (modulus : Nat) (p q : Fin 6)
    (hpair : ∀ i,
      (X i).val % modulus = (X p).val % modulus ∨
        (X i).val % modulus = (X q).val % modulus) :
    classCount (z36RawSetV75Fix X) modulus ≤ 2 := by
  unfold classCount z36RawSetV75Fix
  rw [← List.ofFn_comp']
  simp only [z36RawPointV75Fix_val]
  apply eraseDups_length_le_two_of_pair_v75Fix
  rw [List.forall_mem_ofFn_iff]
  exact hpair

/-- Projective coverage of the Fourier rows is exactly the first raw
`classCount ≤ 2` alternative. -/
theorem z36FourierBlockV74Fix_rows_classCount_le_two_v75Fix
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hrows : Z180K30RowsCoveredByTwoProjectiveV73Fix
      (z36FourierBlockV74Fix U V) p q) :
    classCount (z36RawSetV75Fix U)
      (36 / differenceGcd (z36RawSetV75Fix V)) ≤ 2 := by
  apply classCount_z36RawSetV75Fix_le_two_of_pair_v75Fix U _ p q
  intro i
  rcases hrows i with ⟨scale, hrow⟩ | ⟨scale, hrow⟩
  · left
    exact z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
      (U i) (U p) V
      (z36FourierBlockV74Fix_row_proportional_zero
        U V i p scale hrow)
  · right
    exact z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
      (U i) (U q) V
      (z36FourierBlockV74Fix_row_proportional_zero
        U V i q scale hrow)

/-- Projective coverage of the Fourier columns is exactly the second raw
`classCount ≤ 2` alternative. -/
theorem z36FourierBlockV74Fix_columns_classCount_le_two_v75Fix
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hcolumns : Z180K30ColumnsCoveredByTwoProjectiveV73Fix
      (z36FourierBlockV74Fix U V) p q) :
    classCount (z36RawSetV75Fix V)
      (36 / differenceGcd (z36RawSetV75Fix U)) ≤ 2 := by
  apply classCount_z36RawSetV75Fix_le_two_of_pair_v75Fix V _ p q
  intro l
  rcases hcolumns l with ⟨scale, hcolumn⟩ | ⟨scale, hcolumn⟩
  · left
    apply z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
      (V l) (V p) U
    intro a
    simpa only [mul_comm] using
      z36FourierBlockV74Fix_column_proportional_zero
        U V l p scale hcolumn a
  · right
    apply z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
      (V l) (V q) U
    intro a
    simpa only [mul_comm] using
      z36FourierBlockV74Fix_column_proportional_zero
        U V l q scale hcolumn a

/-- The projective dichotomy of V74 implies the exact raw disjunction. -/
theorem z36FourierBlockV74Fix_classCount_dichotomy_v75Fix
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hprojective :
      Z180K30RowsCoveredByTwoProjectiveV73Fix
          (z36FourierBlockV74Fix U V) p q ∨
        ∃ c d : Fin 6,
          Z180K30ColumnsCoveredByTwoProjectiveV73Fix
            (z36FourierBlockV74Fix U V) c d) :
    classCount (z36RawSetV75Fix U)
          (36 / differenceGcd (z36RawSetV75Fix V)) ≤ 2 ∨
      classCount (z36RawSetV75Fix V)
          (36 / differenceGcd (z36RawSetV75Fix U)) ≤ 2 := by
  rcases hprojective with hrows | ⟨c, d, hcolumns⟩
  · exact Or.inl
      (z36FourierBlockV74Fix_rows_classCount_le_two_v75Fix
        U V p q hrows)
  · exact Or.inr
      (z36FourierBlockV74Fix_columns_classCount_le_two_v75Fix
        U V c d hcolumns)

/-- Boolean endpoint consumed by `exceptionalPairB`. -/
theorem z36FourierBlockV74Fix_rankTwoProjectiveCoverB_v75Fix
    (U V : Fin 6 → ZMod 36) (p q : Fin 6)
    (hprojective :
      Z180K30RowsCoveredByTwoProjectiveV73Fix
          (z36FourierBlockV74Fix U V) p q ∨
        ∃ c d : Fin 6,
          Z180K30ColumnsCoveredByTwoProjectiveV73Fix
            (z36FourierBlockV74Fix U V) c d) :
    rankTwoProjectiveCoverB (z36RawSetV75Fix U) (z36RawSetV75Fix V) = true := by
  rcases z36FourierBlockV74Fix_classCount_dichotomy_v75Fix
      U V p q hprojective with hU | hV
  · simp [rankTwoProjectiveCoverB, hU]
  · simp [rankTwoProjectiveCoverB, hV]

/-- Fully assembled endpoint from an explicit two-row spanning formula. -/
theorem z36FourierBlockV74Fix_rankTwoProjectiveCoverB_of_span_two_v75Fix
    (U V : Fin 6 → ZMod 36)
    (p q : Fin 6) (alpha beta : Fin 6 → Complex)
    (hspan : ∀ i j,
      z36FourierBlockV74Fix U V i j =
        alpha i * z36FourierBlockV74Fix U V p j +
          beta i * z36FourierBlockV74Fix U V q j) :
    rankTwoProjectiveCoverB (z36RawSetV75Fix U) (z36RawSetV75Fix V) = true := by
  apply z36FourierBlockV74Fix_rankTwoProjectiveCoverB_v75Fix U V p q
  exact z36FourierBlockV74Fix_projective_dichotomy_of_span_two
    U V p q alpha beta hspan

#print axioms z36_dvd_mul_natAbsDiff_of_mul_sub_eq_zero_v75Fix
#print axioms z36_val_mod_div_differenceGcd_eq_of_mul_sub_zero_v75Fix
#print axioms z36FourierBlockV74Fix_classCount_dichotomy_v75Fix
#print axioms z36FourierBlockV74Fix_rankTwoProjectiveCoverB_of_span_two_v75Fix

end Fuglede

