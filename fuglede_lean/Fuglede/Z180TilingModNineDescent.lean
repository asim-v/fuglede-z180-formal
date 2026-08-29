import Fuglede.FiniteTilingDilation
import Fuglede.Z180TilingSpectralLargePrimeComplements
import Mathlib.Tactic

/-! # Descent of cardinalities prime to three from ZMod 180 to ZMod 20

Two successive prime dilations by three put the tile inside the subgroup of
multiples of nine, canonically identified with `ZMod 20`.
-/

namespace Fuglede

private def z180IntScaleNine : ℤ →+ ZMod 180 where
  toFun x := (9 * x : ℤ)
  map_zero' := by simp
  map_add' x y := by push_cast; ring

/-- Multiplication by nine from `ZMod 20` into `ZMod 180`. -/
def z20ScaleNine : ZMod 20 →+ ZMod 180 :=
  ZMod.lift 20
    ⟨z180IntScaleNine, by
      change ((180 : ℤ) : ZMod 180) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd 180 180).mpr dvd_rfl⟩

@[simp]
theorem z20ScaleNine_intCast (x : ℤ) :
    z20ScaleNine (x : ZMod 20) = (9 * x : ℤ) := by
  simp [z20ScaleNine, z180IntScaleNine, mul_comm]

theorem z20ScaleNine_injective : Function.Injective z20ScaleNine := by
  rw [z20ScaleNine, ZMod.lift_injective]
  intro m hm
  have hd : (180 : ℤ) ∣ 9 * m := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (9 * m) 180).mp
    exact hm
  obtain ⟨k, hk⟩ := hd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m 20).mpr
  exact ⟨k, by omega⟩

/-- The quotient map reducing a residue modulo 20. -/
def z180TileProjection20 : ZMod 180 →+ ZMod 20 :=
  (ZMod.castHom (by norm_num : 20 ∣ 180) (ZMod 20)).toAddMonoidHom

@[simp]
theorem z180TileProjection20_apply (x : ZMod 180) :
    z180TileProjection20 x = ZMod.cast x := rfl

@[simp]
theorem z20ScaleNine_projection20 (x : ZMod 180) :
    z20ScaleNine (z180TileProjection20 x) = 9 • x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  simp [z180TileProjection20, z20ScaleNine_intCast,
    mul_comm, nsmul_eq_mul]

def z180MultiplesNine : AddSubgroup (ZMod 180) := z20ScaleNine.range

noncomputable def z20EquivMultiplesNine :
    ZMod 20 ≃+ z180MultiplesNine :=
  AddEquiv.ofBijective z20ScaleNine.rangeRestrict
    ⟨fun _ _ h ↦ z20ScaleNine_injective (Subtype.ext_iff.mp h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := x.2
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem z20EquivMultiplesNine_apply (x : ZMod 20) :
    ((z20EquivMultiplesNine x : z180MultiplesNine) : ZMod 180) =
      z20ScaleNine x := rfl

/-- A tile whose cardinality is prime to three descends injectively to an
exact tile of `ZMod 20`. -/
theorem z180_tile_descends_to_z20_of_three_not_dvd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬3 ∣ A.card) :
    ∃ C : Finset (ZMod 20),
      Tiles (A.image z180TileProjection20) C ∧
      (A.image z180TileProjection20).card = A.card := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let A3 : Finset (ZMod 180) := A.image (fun a ↦ 3 • a)
  have hTiles3 : Tiles A3 B := by
    simpa [A3] using
      tiles_image_prime_nsmul_left_of_not_dvd_card 3 hTiles hnot
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  have hprod3 : A3.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles3
  have hBpos : 0 < B.card := by
    obtain ⟨q, hq⟩ := hTiles.2 0
    exact Finset.card_pos.mpr
      ⟨q.1.2, (Finset.mem_product.mp q.2).2⟩
  have hcardA3 : A3.card = A.card := by
    exact (Nat.eq_of_mul_eq_mul_right hBpos
      (hprod.trans hprod3.symm)).symm
  have hnot3 : ¬3 ∣ A3.card := by simpa [hcardA3] using hnot
  let A9 : Finset (ZMod 180) := A3.image (fun a ↦ 3 • a)
  have hTiles9 : Tiles A9 B := by
    simpa [A9] using
      tiles_image_prime_nsmul_left_of_not_dvd_card 3 hTiles3 hnot3
  have hprod9 : A9.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles9
  have hcardA9 : A9.card = A.card := by
    exact (Nat.eq_of_mul_eq_mul_right hBpos
      (hprod.trans hprod9.symm)).symm
  have hA9eq : A9 = A.image (fun a : ZMod 180 ↦ 9 • a) := by
    simp only [A9, A3, Finset.image_image]
    apply Finset.image_congr
    intro a ha
    dsimp
    rw [← mul_nsmul]
  have hnineInj : Set.InjOn (fun a : ZMod 180 ↦ 9 • a) A := by
    apply Finset.card_image_iff.mp
    rw [← hA9eq]
    exact hcardA9
  have hprojectionInj : Set.InjOn z180TileProjection20 A := by
    intro a ha b hb hab
    apply hnineInj ha hb
    have h := congrArg z20ScaleNine hab
    simpa only [z20ScaleNine_projection20] using h
  have hprojectionCard :
      (A.image z180TileProjection20).card = A.card :=
    Finset.card_image_of_injOn hprojectionInj
  have hA9sub : ∀ x ∈ A9, x ∈ z180MultiplesNine := by
    intro x hx
    rw [hA9eq] at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    change 9 • a ∈ z20ScaleNine.range
    exact ⟨z180TileProjection20 a, z20ScaleNine_projection20 a⟩
  let AH : Finset z180MultiplesNine :=
    finsetInAddSubgroup z180MultiplesNine A9
  let BH : Finset z180MultiplesNine :=
    finsetInAddSubgroup z180MultiplesNine B
  have hH : Tiles AH BH := by
    simpa [AH, BH] using
      tiles_restrict_to_addSubgroup z180MultiplesNine hA9sub hTiles9
  let e : ZMod 20 ≃+ z180MultiplesNine := z20EquivMultiplesNine
  have h20 : Tiles (AH.image e.symm) (BH.image e.symm) :=
    tiles_image_addEquiv e.symm hH
  have hfirst : AH.image e.symm = A.image z180TileProjection20 := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyA9 : (y.1 : ZMod 180) ∈ A9 :=
        (mem_finsetInAddSubgroup z180MultiplesNine A9 y).mp
          (by simpa [AH] using hy)
      rw [hA9eq] at hyA9
      obtain ⟨a, ha, ha9⟩ := Finset.mem_image.mp hyA9
      apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      apply e.injective
      apply Subtype.ext
      simp only [e, z20EquivMultiplesNine_apply,
        AddEquiv.apply_symm_apply]
      rw [z20ScaleNine_projection20, ← ha9]
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨e (z180TileProjection20 a), ?_, e.symm_apply_apply _⟩
      apply (mem_finsetInAddSubgroup z180MultiplesNine A9 _).mpr
      simp only [e, z20EquivMultiplesNine_apply]
      rw [z20ScaleNine_projection20, hA9eq]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact ⟨BH.image e.symm, by simpa [hfirst] using h20, hprojectionCard⟩

/-- Scaling a frequency by nine is dual to reducing the point modulo 20. -/
theorem z180_stdAddChar_mul_scaleNine_eq
    (x : ZMod 180) (d : ZMod 20) :
    ZMod.stdAddChar (x * z20ScaleNine d) =
      ZMod.stdAddChar ((z180TileProjection20 x) * d) := by
  calc
    ZMod.stdAddChar (x * z20ScaleNine d) =
        ZMod.stdAddChar
          ((x.val : ZMod 180) * ((9 * d.val : ℕ) : ZMod 180)) := by
      rw [ZMod.natCast_zmod_val]
      congr 1
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (9 * (d.val : ℤ)) : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (9 * (d.val : ℤ)) : ℤ) : ℂ) / (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (d.val : ℤ) : ℤ) : ℂ) / (20 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (d.val : ℤ) : ℤ) : ZMod 20)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar ((z180TileProjection20 x) * d) := by
      congr 1
      push_cast
      rw [z180TileProjection20_apply, ZMod.cast_eq_val,
        ZMod.natCast_zmod_val]

theorem fourierSum_image_projection20
    (A : Finset (ZMod 180)) (d : ZMod 20)
    (hinj : Set.InjOn z180TileProjection20 A) :
    fourierSum (A.image z180TileProjection20) d =
      fourierSum A (z20ScaleNine d) := by
  rw [fourierSum_eq_finset_sum, fourierSum_eq_finset_sum]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro a ha
  exact (z180_stdAddChar_mul_scaleNine_eq a d).symm

end Fuglede
