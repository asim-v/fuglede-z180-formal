import Fuglede.Z180K30DephasedFourierBlockV51
import Fuglede.Z180K30ExceptionalRawFibreV63Fix
import Mathlib.Tactic

/-!
# Exact raw form of the dephased K30 blocks

The row fibre is the projected `A` fibre twisted by the unit `29` in
`ZMod 36`; the column fibre is the untwisted projected `L` fibre.  The main
result identifies every entry of the analytic block from V51 with the
standard `ZMod 36` character of the corresponding raw product.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2
open scoped ComplexConjugate

noncomputable section

/-- Multiplication by `29` is a permutation of `ZMod 36` (inverse `5`). -/
theorem z180K30Unit29_mul_injective_v69 :
    Function.Injective (fun q : ZMod 36 => (29 : ZMod 36) * q) := by
  intro x y hxy
  have h529 : (5 : ZMod 36) * (29 : ZMod 36) = 1 := by
    decide
  calc
    x = (1 : ZMod 36) * x := (one_mul x).symm
    _ = ((5 : ZMod 36) * (29 : ZMod 36)) * x := by rw [h529]
    _ = (5 : ZMod 36) * ((29 : ZMod 36) * x) := by rw [mul_assoc]
    _ = (5 : ZMod 36) * ((29 : ZMod 36) * y) :=
      congrArg (fun q : ZMod 36 => (5 : ZMod 36) * q) hxy
    _ = ((5 : ZMod 36) * (29 : ZMod 36)) * y := by rw [mul_assoc]
    _ = (1 : ZMod 36) * y := by rw [h529]
    _ = y := one_mul y

/-- The `a`-th raw point in the twisted row fibre `U_r`. -/
noncomputable def z180K30ExceptionalRawRowPointV69
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r : Fin 5) (a : Fin 6) : RawPoint :=
  z180K30RawPointV63Fix
    ((29 : ZMod 36) *
      z180K30ProjectedFibreEnumV57 A r (data.cardA r) a)

/-- The `l`-th raw point in the untwisted column fibre `V_s`. -/
noncomputable def z180K30ExceptionalRawColumnPointV69
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) (l : Fin 6) : RawPoint :=
  z180K30RawPointV63Fix
    (z180K30ProjectedFibreEnumV57 L s (data.cardL s) l)

@[simp]
theorem z180K30ExceptionalRawRowPointV69_val
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r : Fin 5) (a : Fin 6) :
    ((z180K30ExceptionalRawRowPointV69 data r a).val : ZMod 36) =
      (29 : ZMod 36) *
        z180K30ProjectedFibreEnumV57 A r (data.cardA r) a := by
  exact z180K30RawPointV63Fix_val _

@[simp]
theorem z180K30ExceptionalRawColumnPointV69_val
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) (l : Fin 6) :
    ((z180K30ExceptionalRawColumnPointV69 data s l).val : ZMod 36) =
      z180K30ProjectedFibreEnumV57 L s (data.cardL s) l := by
  exact z180K30RawPointV63Fix_val _

/-- Twisted projected row fibre `U_r`, in the raw certificate format. -/
noncomputable def z180K30ExceptionalRawRowV69
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r : Fin 5) : RawSet :=
  List.ofFn fun a : Fin 6 =>
    z180K30ExceptionalRawRowPointV69 data r a

/-- Untwisted projected column fibre `V_s`, in the raw certificate format. -/
noncomputable def z180K30ExceptionalRawColumnV69
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5) : RawSet :=
  z180K30RawFibreV63Fix L s (data.cardL s)

theorem z180K30ExceptionalRawRowV69_nodup
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r : Fin 5) :
    (z180K30ExceptionalRawRowV69 data r).Nodup := by
  unfold z180K30ExceptionalRawRowV69
  apply List.nodup_ofFn.mpr
  intro a b hab
  apply z180K30ProjectedFibreEnumV57_injective A r (data.cardA r)
  apply z180K30Unit29_mul_injective_v69
  have hvals :=
    congrArg (fun p : RawPoint => (p.val : ZMod 36)) hab
  simpa only [z180K30ExceptionalRawRowPointV69_val] using hvals

private theorem eraseDups_eq_self_of_nodup_v69
    {l : List RawPoint} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at h
      have hfilter : (l.filter fun b => !b == a) = l := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hba : b != a := by
          intro hba
          apply h.1
          simpa [hba] using hb
        simp [hba]
      rw [List.eraseDups_cons, hfilter, ih h.2]

theorem z180K30ExceptionalRawRowV69_validSixSetB
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r : Fin 5) :
    validSixSetB (z180K30ExceptionalRawRowV69 data r) = true := by
  unfold validSixSetB
  rw [eraseDups_eq_self_of_nodup_v69
    (z180K30ExceptionalRawRowV69_nodup data r)]
  simp [z180K30ExceptionalRawRowV69]

theorem z180K30ExceptionalRawColumnV69_validSixSetB
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5) :
    validSixSetB (z180K30ExceptionalRawColumnV69 data s) = true := by
  simpa [z180K30ExceptionalRawColumnV69] using
    z180K30RawFibreV63Fix_validSixSetB L s (data.cardL s)

/-- The fifth-coordinate component of a block entry is exactly its V51
dephasing phase. -/
private theorem z180K30FifthPhaseCharacterV69
    (x : ZMod 180) (r s : Fin 5)
    (hx : (ZMod.cast x : ZMod 5) = (r.val : ZMod 5)) :
    ZMod.stdAddChar
        (x * ((36 : ZMod 180) * (s.val : ZMod 180))) =
      ZMod.stdAddChar
        ((r.val : ZMod 5) * (s.val : ZMod 5)) := by
  calc
    ZMod.stdAddChar
          (x * ((36 : ZMod 180) * (s.val : ZMod 180))) =
        z180StandardCRTCharacterPairing (toCRT180 x)
          (crt180FifthSingle (s.val : ZMod 5)) := by
      simp only [z180StandardCRTCharacterPairing, fromCRT180_mul,
        fromCRT180_fifthSingle, fromCRT180_toCRT180,
        ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt]
      congr 1
      ring
    _ = ZMod.stdAddChar
        ((r.val : ZMod 5) * (s.val : ZMod 5)) := by
      have hphase :=
        z180StandardCRTCharacterPairing_add_piSingle_two
          (toCRT180 x) (0 : CRT180) (s.val : ZMod 5)
      rw [zero_add] at hphase
      have hzero :
          z180StandardCRTCharacterPairing (toCRT180 x) (0 : CRT180) = 1 := by
        simp [z180StandardCRTCharacterPairing]
      rw [hzero, one_mul, crt180FifthCoord_toCRT180, hx] at hphase
      calc
        z180StandardCRTCharacterPairing (toCRT180 x)
            (crt180FifthSingle (s.val : ZMod 5)) =
          ZMod.stdAddChar
            ((s.val : ZMod 5) * (r.val : ZMod 5)) := hphase
        _ = ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5)) := by
          congr 1
          ring

/-- Removing the fifth-coordinate phase leaves exactly the twisted
`ZMod 36` character. -/
private theorem z180K30DephasedCharacterV69
    (x y : ZMod 180) (r s : Fin 5)
    (hx : (ZMod.cast x : ZMod 5) = (r.val : ZMod 5))
    (hy : (ZMod.cast y : ZMod 5) = (s.val : ZMod 5)) :
    star (ZMod.stdAddChar
        ((r.val : ZMod 5) * (s.val : ZMod 5))) *
        ZMod.stdAddChar (x * y) =
      ZMod.stdAddChar
        (((29 : ZMod 36) * z180K30Projection36 x) *
          z180K30Projection36 y) := by
  let c : ZMod 180 := (36 : ZMod 180) * (s.val : ZMod 180)
  let y0 : ZMod 180 := y - c
  have hsCast :
      (ZMod.cast (s.val : ZMod 180) : ZMod 5) =
        (s.val : ZMod 5) := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt] using
      (ZMod.cast_cast_zmod_of_le (by norm_num : 5 <= 180)
        (s.val : ZMod 5))
  have hy0 : (ZMod.cast y0 : ZMod 5) = 0 := by
    dsimp only [y0, c]
    rw [ZMod.cast_sub (by norm_num : 5 | 180),
      ZMod.cast_mul (by norm_num : 5 | 180), hy]
    have h36 : (ZMod.cast (36 : ZMod 180) : ZMod 5) = 1 := by
      decide
    rw [h36, one_mul, hsCast, sub_self]
  have hyProjection :
      z180K30Projection36 y0 = z180K30Projection36 y := by
    change (ZMod.cast y0 : ZMod 36) = (ZMod.cast y : ZMod 36)
    dsimp only [y0, c]
    rw [ZMod.cast_sub (by norm_num : 36 | 180),
      ZMod.cast_mul (by norm_num : 36 | 180)]
    have h36 : (ZMod.cast (36 : ZMod 180) : ZMod 36) = 0 := by
      decide
    rw [h36, zero_mul, sub_zero]
  have hlift :
      z180K30LiftFrequency36
          ((29 : ZMod 36) * z180K30Projection36 y) = y0 := by
    simpa only [hyProjection] using
      z180K30LiftFrequency36_unit29_projection_v57 y0 hy0
  have hyDecomp : y = y0 + c := by
    dsimp only [y0]
    ring
  have hphase :
      ZMod.stdAddChar (x * c) =
        ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5)) := by
    simpa only [c] using z180K30FifthPhaseCharacterV69 x r s hx
  have hsplit :
      ZMod.stdAddChar (x * y) =
        ZMod.stdAddChar
            (z180K30Projection36 x *
              ((29 : ZMod 36) * z180K30Projection36 y)) *
          ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5)) := by
    calc
      ZMod.stdAddChar (x * y) =
          ZMod.stdAddChar (x * (y0 + c)) := by rw [hyDecomp]
      _ = ZMod.stdAddChar (x * y0 + x * c) := by
        congr 1
        ring
      _ = ZMod.stdAddChar (x * y0) * ZMod.stdAddChar (x * c) := by
        rw [AddChar.map_add_eq_mul]
      _ = ZMod.stdAddChar
            (x * z180K30LiftFrequency36
              ((29 : ZMod 36) * z180K30Projection36 y)) *
          ZMod.stdAddChar (x * c) := by rw [hlift]
      _ = ZMod.stdAddChar
            (z180K30Projection36 x *
              ((29 : ZMod 36) * z180K30Projection36 y)) *
          ZMod.stdAddChar (x * c) := by
        rw [z180_stdAddChar_mul_liftFrequency36_eq]
      _ = ZMod.stdAddChar
            (z180K30Projection36 x *
              ((29 : ZMod 36) * z180K30Projection36 y)) *
          ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5)) := by rw [hphase]
  have hcancel :
      star (ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5))) *
        ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5)) = 1 := by
    rw [star_stdAddChar, <- AddChar.map_add_eq_mul]
    simp
  rw [hsplit]
  calc
    star (ZMod.stdAddChar
          ((r.val : ZMod 5) * (s.val : ZMod 5))) *
        (ZMod.stdAddChar
            (z180K30Projection36 x *
              ((29 : ZMod 36) * z180K30Projection36 y)) *
          ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5))) =
      ZMod.stdAddChar
          (z180K30Projection36 x *
            ((29 : ZMod 36) * z180K30Projection36 y)) *
        (star (ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5))) *
          ZMod.stdAddChar
            ((r.val : ZMod 5) * (s.val : ZMod 5))) := by ring
    _ = ZMod.stdAddChar
        (z180K30Projection36 x *
          ((29 : ZMod 36) * z180K30Projection36 y)) := by
      rw [hcancel, mul_one]
    _ = ZMod.stdAddChar
        (((29 : ZMod 36) * z180K30Projection36 x) *
          z180K30Projection36 y) := by
      congr 1
      ring

/-- Entrywise identification of the dephased analytic block with the exact
raw `ZMod 36` character matrix. -/
theorem z180K30DephasedFourierBlockV51_apply_raw_v69
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30DephasedFourierBlockV51 data r s a l =
      ZMod.stdAddChar
        (((z180K30ExceptionalRawRowPointV69 data r a).val : ZMod 36) *
          ((z180K30ExceptionalRawColumnPointV69 data s l).val : ZMod 36)) := by
  simp only [z180K30DephasedFourierBlockV51, Matrix.smul_apply,
    smul_eq_mul, z180K30OriginalFourierBlockV32_apply,
    z180K30DephasingPhaseV51,
    z180K30ExceptionalRawRowPointV69_val,
    z180K30ExceptionalRawColumnPointV69_val]
  exact z180K30DephasedCharacterV69
    (z180K30OriginalFibreEnumV32 A r (data.cardA r) a)
    (z180K30OriginalFibreEnumV32 L s (data.cardL s) l)
    r s
    (z180K30OriginalFibreEnumV32_fifth A r (data.cardA r) a)
    (z180K30OriginalFibreEnumV32_fifth L s (data.cardL s) l)

#print axioms z180K30ExceptionalRawRowV69_validSixSetB
#print axioms z180K30ExceptionalRawColumnV69_validSixSetB
#print axioms z180K30DephasedFourierBlockV51_apply_raw_v69

end
end Fuglede
