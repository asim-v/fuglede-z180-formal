import Fuglede.FiniteTilingDilation
import Fuglede.Z180TilingSpectralLargePrimeComplements
import Mathlib.Tactic

/-!
# Descent of tiles from ZMod 180 to ZMod 36

If five does not divide the cardinality of a tile, prime dilation by five
preserves its tiling.  The dilated tile lies in the subgroup of multiples of
five, canonically identified with `ZMod 36`.
-/

namespace Fuglede

private def z180IntScaleFive : ℤ →+ ZMod 180 where
  toFun x := (5 * x : ℤ)
  map_zero' := by simp
  map_add' x y := by push_cast; ring

/-- Multiplication by five from `ZMod 36` into `ZMod 180`. -/
def z36ScaleFive : ZMod 36 →+ ZMod 180 :=
  ZMod.lift 36
    ⟨z180IntScaleFive, by
      change ((180 : ℤ) : ZMod 180) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd 180 180).mpr dvd_rfl⟩

@[simp]
theorem z36ScaleFive_intCast (x : ℤ) :
    z36ScaleFive (x : ZMod 36) = (5 * x : ℤ) := by
  simp [z36ScaleFive, z180IntScaleFive, mul_comm]

theorem z36ScaleFive_injective : Function.Injective z36ScaleFive := by
  rw [z36ScaleFive, ZMod.lift_injective]
  intro m hm
  have hd : (180 : ℤ) ∣ 5 * m := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * m) 180).mp
    exact hm
  obtain ⟨k, hk⟩ := hd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m 36).mpr
  exact ⟨k, by omega⟩

/-- The quotient map reducing a residue modulo 36. -/
def z180TileProjection36 : ZMod 180 →+ ZMod 36 :=
  (ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod 36)).toAddMonoidHom

@[simp]
theorem z180TileProjection36_apply (x : ZMod 180) :
    z180TileProjection36 x = ZMod.cast x := rfl

@[simp]
theorem z36ScaleFive_projection36 (x : ZMod 180) :
    z36ScaleFive (z180TileProjection36 x) = 5 • x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  simp [z180TileProjection36, z36ScaleFive_intCast,
    mul_comm, nsmul_eq_mul]

/-- The subgroup of multiples of five in `ZMod 180`. -/
def z180MultiplesFive : AddSubgroup (ZMod 180) := z36ScaleFive.range

/-- Canonical equivalence between `ZMod 36` and the multiples of five. -/
noncomputable def z36EquivMultiplesFive :
    ZMod 36 ≃+ z180MultiplesFive :=
  AddEquiv.ofBijective z36ScaleFive.rangeRestrict
    ⟨fun _ _ h ↦ z36ScaleFive_injective (Subtype.ext_iff.mp h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := x.2
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem z36EquivMultiplesFive_apply (x : ZMod 36) :
    ((z36EquivMultiplesFive x : z180MultiplesFive) : ZMod 180) =
      z36ScaleFive x := rfl

/-- A tile whose cardinality is prime to five descends injectively to an
exact tile of `ZMod 36`. -/
theorem z180_tile_descends_to_z36_of_five_not_dvd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬5 ∣ A.card) :
    ∃ C : Finset (ZMod 36),
      Tiles (A.image z180TileProjection36) C ∧
      (A.image z180TileProjection36).card = A.card := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A5 : Finset (ZMod 180) := A.image (fun a ↦ 5 • a)
  have hTiles5 : Tiles A5 B := by
    simpa [A5] using
      tiles_image_prime_nsmul_left_of_not_dvd_card 5 hTiles hnot
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  have hprod5 : A5.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles5
  have hBpos : 0 < B.card := by
    obtain ⟨q, hq⟩ := hTiles.2 0
    exact (Finset.card_pos.mpr
      ⟨q.1.2, (Finset.mem_product.mp q.2).2⟩)
  have hcardA5 : A5.card = A.card := by
    exact (Nat.eq_of_mul_eq_mul_right hBpos
      (hprod.trans hprod5.symm)).symm
  have hfiveInj : Set.InjOn (fun a : ZMod 180 ↦ 5 • a) A := by
    apply Finset.card_image_iff.mp
    simpa [A5] using hcardA5
  have hprojectionInj : Set.InjOn z180TileProjection36 A := by
    intro a ha b hb hab
    apply hfiveInj ha hb
    have h := congrArg z36ScaleFive hab
    simpa only [z36ScaleFive_projection36] using h
  have hprojectionCard :
      (A.image z180TileProjection36).card = A.card :=
    Finset.card_image_of_injOn hprojectionInj
  have hA5sub : ∀ x ∈ A5, x ∈ z180MultiplesFive := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    change 5 • a ∈ z36ScaleFive.range
    exact ⟨z180TileProjection36 a, z36ScaleFive_projection36 a⟩
  let AH : Finset z180MultiplesFive :=
    finsetInAddSubgroup z180MultiplesFive A5
  let BH : Finset z180MultiplesFive :=
    finsetInAddSubgroup z180MultiplesFive B
  have hH : Tiles AH BH := by
    simpa [AH, BH] using
      tiles_restrict_to_addSubgroup z180MultiplesFive hA5sub hTiles5
  let e : ZMod 36 ≃+ z180MultiplesFive := z36EquivMultiplesFive
  have h36 : Tiles (AH.image e.symm) (BH.image e.symm) :=
    tiles_image_addEquiv e.symm hH
  have hfirst : AH.image e.symm = A.image z180TileProjection36 := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyA5 : (y.1 : ZMod 180) ∈ A5 :=
        (mem_finsetInAddSubgroup z180MultiplesFive A5 y).mp
          (by simpa [AH] using hy)
      obtain ⟨a, ha, ha5⟩ := Finset.mem_image.mp hyA5
      apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      apply e.injective
      apply Subtype.ext
      simp only [e, z36EquivMultiplesFive_apply,
        AddEquiv.apply_symm_apply]
      rw [z36ScaleFive_projection36, ← ha5]
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨e (z180TileProjection36 a), ?_, e.symm_apply_apply _⟩
      apply (mem_finsetInAddSubgroup z180MultiplesFive A5 _).mpr
      simp only [e, z36EquivMultiplesFive_apply]
      rw [z36ScaleFive_projection36]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact ⟨BH.image e.symm, by simpa [hfirst] using h36, hprojectionCard⟩

/-- Scaling a frequency by five is dual to reducing the point modulo 36. -/
theorem z180_stdAddChar_mul_scaleFive_eq
    (x : ZMod 180) (d : ZMod 36) :
    ZMod.stdAddChar (x * z36ScaleFive d) =
      ZMod.stdAddChar ((z180TileProjection36 x) * d) := by
  calc
    ZMod.stdAddChar (x * z36ScaleFive d) =
        ZMod.stdAddChar
          ((x.val : ZMod 180) * ((5 * d.val : ℕ) : ZMod 180)) := by
      rw [ZMod.natCast_zmod_val]
      congr 1
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (5 * (d.val : ℤ)) : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (5 * (d.val : ℤ)) : ℤ) : ℂ) / (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (d.val : ℤ) : ℤ) : ℂ) / (36 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (d.val : ℤ) : ℤ) : ZMod 36)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar ((z180TileProjection36 x) * d) := by
      congr 1
      push_cast
      rw [z180TileProjection36_apply, ZMod.cast_eq_val,
        ZMod.natCast_zmod_val]

theorem fourierSum_image_projection36
    (A : Finset (ZMod 180)) (d : ZMod 36)
    (hinj : Set.InjOn z180TileProjection36 A) :
    fourierSum (A.image z180TileProjection36) d =
      fourierSum A (z36ScaleFive d) := by
  rw [fourierSum_eq_finset_sum, fourierSum_eq_finset_sum]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro a ha
  exact (z180_stdAddChar_mul_scaleFive_eq a d).symm

end Fuglede
