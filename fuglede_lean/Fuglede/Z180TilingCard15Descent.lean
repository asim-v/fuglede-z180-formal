import Fuglede.FiniteTilingDilation
import Fuglede.Z180TilingSpectralLargePrimeComplements
import Mathlib.Tactic

/-!
# Descent of a fifteen-point tile from ZMod 180 to ZMod 45

The odd-cardinality dilation theorem removes the two-power part of the
ambient modulus.  This module packages the subgroup restriction and the
identification between ZMod 45 and 4 times ZMod 180.
-/

namespace Fuglede

private def z180IntScaleFour : ℤ →+ ZMod 180 where
  toFun x := (4 * x : ℤ)
  map_zero' := by simp
  map_add' x y := by
    push_cast
    ring

/-- Multiplication by four, viewed as an additive embedding from ZMod 45
into ZMod 180. -/
def z45ScaleFour : ZMod 45 →+ ZMod 180 :=
  ZMod.lift 45
    ⟨z180IntScaleFour, by
      change ((180 : ℤ) : ZMod 180) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd 180 180).mpr dvd_rfl⟩

@[simp]
theorem z45ScaleFour_intCast (x : ℤ) :
    z45ScaleFour (x : ZMod 45) = (4 * x : ℤ) := by
  simp [z45ScaleFour, z180IntScaleFour, mul_comm]

theorem z45ScaleFour_injective : Function.Injective z45ScaleFour := by
  rw [z45ScaleFour, ZMod.lift_injective]
  intro m hm
  have hd : (180 : ℤ) ∣ 4 * m := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * m) 180).mp
    exact hm
  have hd45 : (45 : ℤ) ∣ m := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨k, ?_⟩
    omega
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m 45).mpr hd45

/-- The subgroup of multiples of four in ZMod 180. -/
def z180MultiplesFour : AddSubgroup (ZMod 180) :=
  z45ScaleFour.range

/-- Canonical additive equivalence between ZMod 45 and the multiples of four. -/
noncomputable def z45EquivMultiplesFour :
    ZMod 45 ≃+ z180MultiplesFour :=
  AddEquiv.ofBijective z45ScaleFour.rangeRestrict
    ⟨fun _ _ h ↦ z45ScaleFour_injective (Subtype.ext_iff.mp h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := x.2
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem z45EquivMultiplesFour_apply (x : ZMod 45) :
    ((z45EquivMultiplesFour x : z180MultiplesFour) : ZMod 180) =
      z45ScaleFour x := rfl

/-- Reduction modulo forty-five. -/
def z180TileProjection45 : ZMod 180 →+ ZMod 45 :=
  (ZMod.castHom (by norm_num : 45 ∣ 180) (ZMod 45)).toAddMonoidHom

@[simp]
theorem z180TileProjection45_apply (x : ZMod 180) :
    z180TileProjection45 x = ZMod.cast x := rfl

@[simp]
theorem z45ScaleFour_projection45 (x : ZMod 180) :
    z45ScaleFour (z180TileProjection45 x) = 4 • x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  simp [z180TileProjection45, ZMod.castHom_apply,
    z45ScaleFour_intCast, mul_comm, nsmul_eq_mul]

/-- Scaling a frequency by four is dual to reducing the point modulo 45. -/
theorem z180_stdAddChar_mul_scaleFour_eq
    (x : ZMod 180) (d : ZMod 45) :
    ZMod.stdAddChar (x * z45ScaleFour d) =
      ZMod.stdAddChar ((z180TileProjection45 x) * d) := by
  calc
    ZMod.stdAddChar (x * z45ScaleFour d) =
        ZMod.stdAddChar
          ((x.val : ZMod 180) * ((4 * d.val : ℕ) : ZMod 180)) := by
      rw [ZMod.natCast_zmod_val]
      congr 1
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (4 * (d.val : ℤ)) : ℤ) : ZMod 180)) := by
      congr 1
      push_cast
      rfl
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (4 * (d.val : ℤ)) : ℤ) : ℂ) / (180 : ℂ)) :=
      ZMod.stdAddChar_coe _
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (((x.val : ℤ) * (d.val : ℤ) : ℤ) : ℂ) / (45 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar
        ((((x.val : ℤ) * (d.val : ℤ) : ℤ) : ZMod 45)) := by
      symm
      exact ZMod.stdAddChar_coe _
    _ = ZMod.stdAddChar ((z180TileProjection45 x) * d) := by
      congr 1
      push_cast
      rw [z180TileProjection45_apply, ZMod.cast_eq_val,
        ZMod.natCast_zmod_val]

/-- Fourier sums commute with the projection to ZMod 45 when the projection
is injective on the source set. -/
theorem fourierSum_image_projection45
    (A : Finset (ZMod 180)) (d : ZMod 45)
    (hinj : Set.InjOn z180TileProjection45 A) :
    fourierSum (A.image z180TileProjection45) d =
      fourierSum A (z45ScaleFour d) := by
  rw [fourierSum_eq_finset_sum, fourierSum_eq_finset_sum]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro a ha
  exact (z180_stdAddChar_mul_scaleFour_eq a d).symm

/-- A cardinality-fifteen tile descends, after removing the two-primary
part of the modulus, to an exact fifteen-by-three tiling of ZMod 45. -/
theorem z180_card15_tile_descends_to_z45
    {A B : Finset (ZMod 180)} (hcard : A.card = 15)
    (hTiles : Tiles A B) :
    ∃ C : Finset (ZMod 45),
      Tiles (A.image z180TileProjection45) C ∧
      (A.image z180TileProjection45).card = 15 := by
  let double : ZMod 180 → ZMod 180 := fun x ↦ 2 • x
  let A2 : Finset (ZMod 180) := A.image double
  let A4 : Finset (ZMod 180) := A2.image double
  have hOddA : Odd A.card := by rw [hcard]; decide
  have hTiles2 : Tiles A2 B := by
    simpa [A2, double] using
      tiles_image_two_nsmul_left_of_odd_card hTiles hOddA
  have hcardB : B.card = 12 := by
    have h := card_mul_eq_card_of_tiles hTiles
    simp [ZMod.card, hcard] at h
    omega
  have hcardA2 : A2.card = 15 := by
    have h := card_mul_eq_card_of_tiles hTiles2
    simp [ZMod.card, hcardB] at h
    omega
  have hOddA2 : Odd A2.card := by rw [hcardA2]; decide
  have hTiles4 : Tiles A4 B := by
    simpa [A4, double] using
      tiles_image_two_nsmul_left_of_odd_card hTiles2 hOddA2
  have hcardA4 : A4.card = 15 := by
    have h := card_mul_eq_card_of_tiles hTiles4
    simp [ZMod.card, hcardB] at h
    omega
  have hdoubleInjA : Set.InjOn double A := by
    apply Finset.card_image_iff.mp
    simpa [A2, hcard, hcardA2]
  have hdoubleInjA2 : Set.InjOn double A2 := by
    apply Finset.card_image_iff.mp
    simpa [A4, hcardA2, hcardA4]
  have hprojectionInj : Set.InjOn z180TileProjection45 A := by
    intro a ha b hb hab
    have hfour : double (double a) = double (double b) := by
      have h := congrArg z45ScaleFour hab
      have h' : 4 • a = 4 • b := by
        simpa only [z45ScaleFour_projection45] using h
      calc
        double (double a) = 4 • a := by dsimp [double]; module
        _ = 4 • b := h'
        _ = double (double b) := by dsimp [double]; module
    have htwo : double a = double b := by
      apply hdoubleInjA2
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      · exact hfour
    exact hdoubleInjA ha hb htwo
  have hprojectionCard :
      (A.image z180TileProjection45).card = 15 := by
    rw [Finset.card_image_of_injOn hprojectionInj, hcard]
  have hA4sub : ∀ x ∈ A4, x ∈ z180MultiplesFour := by
    intro x hx
    obtain ⟨a2, ha2, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha2
    change 2 • (2 • a) ∈ z45ScaleFour.range
    refine ⟨z180TileProjection45 a, ?_⟩
    rw [z45ScaleFour_projection45]
    module
  let AH : Finset z180MultiplesFour :=
    finsetInAddSubgroup z180MultiplesFour A4
  let BH : Finset z180MultiplesFour :=
    finsetInAddSubgroup z180MultiplesFour B
  have hH : Tiles AH BH := by
    simpa [AH, BH] using
      tiles_restrict_to_addSubgroup z180MultiplesFour hA4sub hTiles4
  let e : ZMod 45 ≃+ z180MultiplesFour := z45EquivMultiplesFour
  have h45 :
      Tiles (AH.image e.symm) (BH.image e.symm) :=
    tiles_image_addEquiv e.symm hH
  have hfirst : AH.image e.symm = A.image z180TileProjection45 := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyA4 : (y.1 : ZMod 180) ∈ A4 :=
        (mem_finsetInAddSubgroup z180MultiplesFour A4 y).mp
          (by simpa [AH] using hy)
      obtain ⟨a2, ha2, ha4⟩ := Finset.mem_image.mp hyA4
      obtain ⟨a, ha, ha2⟩ := Finset.mem_image.mp ha2
      apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      apply e.injective
      apply Subtype.ext
      simp only [e, z45EquivMultiplesFour_apply,
        AddEquiv.apply_symm_apply]
      rw [z45ScaleFour_projection45]
      rw [← ha4, ← ha2]
      module
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨e (z180TileProjection45 a), ?_, e.symm_apply_apply _⟩
      apply (mem_finsetInAddSubgroup z180MultiplesFour A4 _).mpr
      simp only [e, z45EquivMultiplesFour_apply]
      rw [z45ScaleFour_projection45]
      apply Finset.mem_image.mpr
      refine ⟨2 • a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · module
  exact ⟨BH.image e.symm, by simpa [hfirst] using h45, hprojectionCard⟩

/-- A three-term Fourier zero forces the phase difference of any two
distinct points to have additive order three.  This is modulus-independent. -/
theorem triple_fourier_zero_phase_order_three
    {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hzero : fourierSum ({a, b, c} : Finset (ZMod N)) d = 0) :
    addOrderOf ((a - b) * d) = 3 := by
  have hsum :
      ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) +
        ZMod.stdAddChar (c * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [hab, hac, hbc, add_assoc] using hzero
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  let w : ℂ := ZMod.stdAddChar (c * d)
  have hgeom := unit_triple_ratio_order_three
    (stdAddChar_mul_star_self (a * d))
    (stdAddChar_mul_star_self (b * d))
    (stdAddChar_mul_star_self (c * d)) hsum
  let z : ZMod N := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z := by
    calc
      u * star v =
          ZMod.stdAddChar (a * d) * star (ZMod.stdAddChar (b * d)) := rfl
      _ = ZMod.stdAddChar ((a - b) * d) := by
        rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  have hzpow : (ZMod.stdAddChar z) ^ 3 = 1 := by
    rw [← hratio]
    exact hgeom.1
  have hzne : z ≠ 0 := by
    intro hz
    apply hgeom.2.1
    rw [hratio, hz, AddChar.map_zero_eq_one]
  have hzsmul : 3 • z = 0 := by
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_nsmul_eq_pow, hzpow, AddChar.map_zero_eq_one]
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime hzsmul hzne

/-- Fifteen consecutive frequencies in ZMod 45. -/
def z45SpectrumBlock : Finset (ZMod 45) :=
  Finset.image (fun n : ℕ ↦ (n : ZMod 45)) (Finset.range 15)

/-- The subgroup of frequencies divisible by three. -/
def z45SpectrumThreeMultiples : Finset (ZMod 45) :=
  Finset.image (fun n : ℕ ↦ (3 * n : ZMod 45)) (Finset.range 15)

/-- Three adjacent residues in each coset modulo nine. -/
def z45SpectrumThreeByFive : Finset (ZMod 45) :=
  Finset.image (fun p : ℕ × ℕ ↦ (9 * p.1 + p.2 : ZMod 45))
    (Finset.range 5 ×ˢ Finset.range 3)

/-- A fifteen-frequency set selected from the divisibility type of a
nonzero phase difference. -/
def z45SpectrumForDifference (q : ZMod 45) : Finset (ZMod 45) :=
  if 3 ∣ q.val then z45SpectrumThreeMultiples
  else if 5 ∣ q.val then z45SpectrumThreeByFive
  else z45SpectrumBlock

private theorem z45SpectrumBlock_card : z45SpectrumBlock.card = 15 := by decide
private theorem z45SpectrumThreeMultiples_card :
    z45SpectrumThreeMultiples.card = 15 := by decide
private theorem z45SpectrumThreeByFive_card :
    z45SpectrumThreeByFive.card = 15 := by decide

theorem z45SpectrumForDifference_card (q : ZMod 45) :
    (z45SpectrumForDifference q).card = 15 := by
  simp only [z45SpectrumForDifference]
  split
  · exact z45SpectrumThreeMultiples_card
  · split
    · exact z45SpectrumThreeByFive_card
    · exact z45SpectrumBlock_card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem z45_order_three_value
    {x : ZMod 45} (hx : addOrderOf x = 3) :
    x = 15 ∨ x = 30 := by
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [ZMod.addOrderOf_coe x.val (by norm_num)] at hx
  have hlt := x.val_lt
  interval_cases x.val <;> norm_num at hx <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem z45SpectrumForDifference_avoids_order_three_values :
    ∀ q : ZMod 45, q ≠ 0 →
      ∀ l₁ ∈ z45SpectrumForDifference q,
      ∀ l₂ ∈ z45SpectrumForDifference q, l₁ ≠ l₂ →
        q * (l₁ - l₂) ≠ 15 ∧ q * (l₁ - l₂) ≠ 30 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z45SpectrumForDifference_avoids_order_three :
    ∀ q : ZMod 45, q ≠ 0 →
      ∀ l₁ ∈ z45SpectrumForDifference q,
      ∀ l₂ ∈ z45SpectrumForDifference q, l₁ ≠ l₂ →
        addOrderOf (q * (l₁ - l₂)) ≠ 3 := by
  intro q hq l₁ hl₁ l₂ hl₂ hne horder
  rcases z45_order_three_value horder with h15 | h30
  · exact (z45SpectrumForDifference_avoids_order_three_values
      q hq l₁ hl₁ l₂ hl₂ hne).1 h15
  · exact (z45SpectrumForDifference_avoids_order_three_values
      q hq l₁ hl₁ l₂ hl₂ hne).2 h30

/-- Every three-point complement in a 15-by-3 tiling of ZMod 45 supplies a
universal fifteen-point spectrum for the other factor. -/
theorem z45_exists_spectrum_of_tile_card_fifteen
    {A C : Finset (ZMod 45)} (hcard : A.card = 15)
    (hTiles : Tiles A C) :
    ∃ L : Finset (ZMod 45), CyclotomicSpectrum 45 A L := by
  have hcardC : C.card = 3 := by
    have h := card_mul_eq_card_of_tiles hTiles
    simp [ZMod.card, hcard] at h
    omega
  obtain ⟨c₀, c₁, c₂, h01, h02, h12, rfl⟩ :=
    Finset.card_eq_three.mp hcardC
  let q : ZMod 45 := c₀ - c₁
  have hq : q ≠ 0 := sub_ne_zero.mpr h01
  let L := z45SpectrumForDifference q
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨L, cyclotomicSpectrum_of_tiles_of_complement_nonzero
    hTiles hA ?_ ?_⟩
  · rw [hcard, z45SpectrumForDifference_card]
  · intro l₁ hl₁ l₂ hl₂ hlne hzero
    have horder :=
      triple_fourier_zero_phase_order_three h01 h02 h12 hzero
    exact (z45SpectrumForDifference_avoids_order_three
      q hq l₁ hl₁ l₂ hl₂ hlne) (by simpa [q] using horder)

/-- Every fifteen-point translational tile of ZMod 180 is spectral. -/
theorem z180_exists_spectrum_of_tile_card_fifteen
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 15) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨C, hTiles45, hprojectionCard⟩ :=
    z180_card15_tile_descends_to_z45 hcard hTiles
  obtain ⟨L, hSpectrum45⟩ :=
    z45_exists_spectrum_of_tile_card_fifteen hprojectionCard hTiles45
  have hFourier45 :
      FourierSpectrum (A.image z180TileProjection45) L :=
    (cyclotomicSpectrum_iff_fourierSpectrum _ _).mp hSpectrum45
  have hprojectionInj : Set.InjOn z180TileProjection45 A := by
    apply Finset.card_image_iff.mp
    rw [hprojectionCard, hcard]
  let L180 : Finset (ZMod 180) := L.image z45ScaleFour
  refine ⟨L180, (cyclotomicSpectrum_iff_fourierSpectrum _ _).mpr ?_⟩
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨hA, ?_, ?_⟩
  · calc
      A.card = (A.image z180TileProjection45).card := by
        rw [hcard, hprojectionCard]
      _ = L.card := hFourier45.2.1
      _ = L180.card := by
        symm
        exact Finset.card_image_of_injective L z45ScaleFour_injective
  · intro l₁ hl₁ l₂ hl₂ hlne
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₁)
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₂)
    have hdne : d₁ ≠ d₂ := by
      intro h
      subst d₂
      exact hlne rfl
    rw [← map_sub]
    rw [← fourierSum_image_projection45 A (d₁ - d₂) hprojectionInj]
    exact hFourier45.2.2 d₁ hd₁ d₂ hd₂ hdne

#print axioms z45_exists_spectrum_of_tile_card_fifteen
#print axioms z180_exists_spectrum_of_tile_card_fifteen

end Fuglede
