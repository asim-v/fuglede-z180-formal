import Fuglede.Z180TilingCard18Descent

/-! # The cardinality-twelve tiling-to-spectral case

A twelve-point tile in `ZMod 180` descends injectively to a twelve-point tile
in `ZMod 36`.  Its complement there has three points.  A nonzero Fourier zero
of that complement determines an order-three phase subgroup; pulling back a
transversal to this subgroup gives the required twelve frequencies.
-/

namespace Fuglede

private theorem z36_char_unit_three (x : ZMod 36) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

private theorem z36_char_ratio_three (a b d : ZMod 36) :
    ZMod.stdAddChar (a * d) * star (ZMod.stdAddChar (b * d)) =
      ZMod.stdAddChar ((a - b) * d) := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem z36_triple_phase_structure {a b c d : ZMod 36}
    (hzero : ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) +
      ZMod.stdAddChar (c * d) = 0) :
    addOrderOf (z36PhaseHom d a - z36PhaseHom d b) = 3 ∧
      z36PhaseHom d c - z36PhaseHom d a =
        z36PhaseHom d a - z36PhaseHom d b := by
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  let w : ℂ := ZMod.stdAddChar (c * d)
  have hgeom := unit_triple_ratio_order_three
    (z36_char_unit_three (a * d)) (z36_char_unit_three (b * d))
    (z36_char_unit_three (c * d)) hzero
  let z : ZMod 36 := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z :=
    z36_char_ratio_three a b d
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
  let t := z36PhaseHom d a - z36PhaseHom d b
  have htcoe : (t.1 : ZMod 36) = z := by
    change a * d - b * d = (a - b) * d
    ring
  have htne : t ≠ 0 := by
    intro ht0
    apply hzne
    rw [← htcoe]
    exact congrArg Subtype.val ht0
  have htsmul : 3 • t = 0 := by
    apply Subtype.ext
    simpa [htcoe] using hzsmul
  have htorder : addOrderOf t = 3 := by
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact addOrderOf_eq_prime htsmul htne
  refine ⟨htorder, ?_⟩
  apply Subtype.ext
  change c * d - a * d = a * d - b * d
  apply ZMod.injective_stdAddChar
  have hcRatio :
      ZMod.stdAddChar ((c - a) * d) =
        ZMod.stdAddChar ((a - b) * d) := by
    rw [← z36_char_ratio_three c a d, ← z36_char_ratio_three a b d]
    exact hgeom.2.2
  convert hcRatio using 1 <;> ring

private theorem z36_triple_zero_phase_order_three
    {b₀ b₁ b₂ d : ZMod 36} (h01 : b₀ ≠ b₁) (h02 : b₀ ≠ b₂)
    (h12 : b₁ ≠ b₂)
    (hzero : fourierSum ({b₀, b₁, b₂} : Finset (ZMod 36)) d = 0) :
    addOrderOf ((z36PhaseHom (b₀ - b₁)) d) = 3 := by
  have hsum :
      ZMod.stdAddChar (b₀ * d) + ZMod.stdAddChar (b₁ * d) +
        ZMod.stdAddChar (b₂ * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [h01, h02, h12, add_assoc] using hzero
  let s := z36PhaseHom d b₀ - z36PhaseHom d b₁
  let r := z36PhaseHom (b₀ - b₁) d
  have hsorder : addOrderOf s = 3 := (z36_triple_phase_structure hsum).1
  have hsthree : 3 • s = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hsorder]
  have hsne : s ≠ 0 := by
    intro hs
    have hone : addOrderOf s = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hs
    omega
  have hcoe : s.1 = r.1 := by
    change b₀ * d - b₁ * d = d * (b₀ - b₁)
    ring
  have hrne : r ≠ 0 := by
    intro hr
    apply hsne
    apply Subtype.ext
    rw [hcoe]
    exact congrArg Subtype.val hr
  have hrthree : 3 • r = 0 := by
    apply Subtype.ext
    change 3 • r.1 = 0
    rw [← hcoe]
    exact congrArg Subtype.val hsthree
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime hrthree hrne

private theorem z36_eq_twelve_or_twentyFour_of_three_nsmul_eq_zero
    {x : ZMod 36} (hthree : 3 • x = 0) (hxne : x ≠ 0) :
    x = 12 ∨ x = 24 := by
  have hcast : ((3 * x.val : ℕ) : ZMod 36) = 0 := by
    calc
      ((3 * x.val : ℕ) : ZMod 36) = (3 : ZMod 36) * x := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        norm_num
      _ = 3 • x := by simp
      _ = 0 := hthree
  have hdiv : 36 ∣ 3 * x.val :=
    (ZMod.natCast_eq_zero_iff (3 * x.val) 36).mp hcast
  have hxpos : 0 < x.val := by
    exact Nat.pos_of_ne_zero (by
      intro h
      apply hxne
      apply ZMod.val_injective
      simpa [h])
  have hxlt : x.val < 36 := ZMod.val_lt x
  obtain ⟨k, hk⟩ := hdiv
  have hxval : x.val = 12 ∨ x.val = 24 := by omega
  rcases hxval with hxval | hxval
  · left
    calc
      x = (x.val : ZMod 36) := (ZMod.natCast_zmod_val x).symm
      _ = 12 := by rw [hxval]; norm_num
  · right
    calc
      x = (x.val : ZMod 36) := (ZMod.natCast_zmod_val x).symm
      _ = 24 := by rw [hxval]; norm_num

private theorem z36_mem_zmultiples_of_addOrderOf_eq_three
    {H : AddSubgroup (ZMod 36)} {r e : H}
    (hr : addOrderOf r = 3) (he : addOrderOf e = 3) :
    e ∈ AddSubgroup.zmultiples r := by
  have hrthree : 3 • r.1 = (0 : ZMod 36) :=
    congrArg Subtype.val
      (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hr]))
  have hethree : 3 • e.1 = (0 : ZMod 36) :=
    congrArg Subtype.val
      (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [he]))
  have hrne : r.1 ≠ (0 : ZMod 36) := by
    intro h
    have hz : r = 0 := Subtype.ext h
    have hone : addOrderOf r = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hz
    omega
  have hene : e.1 ≠ (0 : ZMod 36) := by
    intro h
    have hz : e = 0 := Subtype.ext h
    have hone : addOrderOf e = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hz
    omega
  rcases z36_eq_twelve_or_twentyFour_of_three_nsmul_eq_zero hrthree hrne with
    hr12 | hr24 <;>
  rcases z36_eq_twelve_or_twentyFour_of_three_nsmul_eq_zero hethree hene with
    he12 | he24
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨1, ?_⟩
    simpa using Subtype.ext (he12.trans hr12.symm).symm
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨2, Subtype.ext ?_⟩
    change (2 : ℤ) • r.1 = e.1
    rw [he24, hr12]
    decide
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨2, Subtype.ext ?_⟩
    change (2 : ℤ) • r.1 = e.1
    rw [he12, hr24]
    decide
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨1, ?_⟩
    simpa using Subtype.ext (he24.trans hr24.symm).symm

/-- Every twelve-point tile of `ZMod 36` is spectral. -/
theorem z36_exists_spectrum_of_tile_card_twelve
    {A B : Finset (ZMod 36)} (hTiles : Tiles A B)
    (hcard : A.card = 12) :
    ∃ L : Finset (ZMod 36), CyclotomicSpectrum 36 A L := by
  have hprod : A.card * B.card = 36 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 3 := by omega
  obtain ⟨b₀, b₁, b₂, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp hBcard
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hAproper : A ≠ Finset.univ := by
    intro h
    subst A
    simp at hcard
  obtain ⟨d₀, hd₀, hBzero⟩ :=
    exists_nonzero_fourier_zero_left_of_tiles (tiles_comm hTiles) hA hAproper
  let t : ZMod 36 := b₀ - b₁
  let H := (z36MulHom t).range
  let ψ : ZMod 36 →+ H := z36PhaseHom t
  let r : H := ψ d₀ - ψ 0
  have hrorder : addOrderOf r = 3 := by
    dsimp [r]
    simpa [ψ, t] using
      z36_triple_zero_phase_order_three h01 h02 h12 hBzero
  let K : AddSubgroup H := AddSubgroup.zmultiples r
  let q : H →+ H ⧸ K := QuotientAddGroup.mk' K
  obtain ⟨C, hKC⟩ := exists_kernel_tiling_complement q
    (QuotientAddGroup.mk'_surjective K)
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (z36MulHom t).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective (z36MulHom t)
  have hstep : ψ (2 • d₀) - ψ d₀ = ψ d₀ - ψ 0 := by
    apply Subtype.ext
    change (2 • d₀) * t - d₀ * t = d₀ * t - 0 * t
    simp [two_nsmul]
    ring
  have hphaseorder : addOrderOf (ψ d₀ - ψ 0) = 3 := hrorder
  have hstructure := triple_image_structure ψ d₀ 0 (2 • d₀) hphaseorder hstep
  have hinj : Set.InjOn ψ
      (({d₀, 0, 2 • d₀} : Finset (ZMod 36)) : Set (ZMod 36)) :=
    hstructure.1
  have himage :
      ({d₀, 0, 2 • d₀} : Finset (ZMod 36)).image ψ = kernelFinset q := by
    rw [hstructure.2]
    change (kernelFinset q).image (fun x => ψ 0 + x) = kernelFinset q
    simp
  let L : Finset (ZMod 36) := preimageFinset ψ C
  have hsmallTiles : Tiles ({d₀, 0, 2 • d₀} : Finset (ZMod 36)) L := by
    dsimp [L]
    apply lift_tiles_of_surjective ψ hψsurj
      ({d₀, 0, 2 • d₀} : Finset (ZMod 36)) C hinj
    rw [himage]
    exact hKC
  have hkcard : (kernelFinset q).card = 3 := by
    change (kernelFinset (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples r))).card = 3
    rw [card_kernelFinset_quotient_zmultiples, hrorder]
  have hDcard : ({d₀, 0, 2 • d₀} : Finset (ZMod 36)).card = 3 := by
    calc
      ({d₀, 0, 2 • d₀} : Finset (ZMod 36)).card =
          (({d₀, 0, 2 • d₀} : Finset (ZMod 36)).image ψ).card :=
        (Finset.card_image_iff.mpr hinj).symm
      _ = (kernelFinset q).card := congrArg Finset.card himage
      _ = 3 := hkcard
  have hLcard : L.card = 12 := by
    have hc := card_mul_eq_card_of_tiles hsmallTiles
    rw [hDcard] at hc
    have hc' : 3 * L.card = 36 := by simpa using hc
    omega
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum ({b₀, b₁, b₂} : Finset (ZMod 36)) (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hne hzero
    have heorder : addOrderOf (ψ (l₁ - l₂)) = 3 := by
      dsimp [ψ, t]
      exact z36_triple_zero_phase_order_three h01 h02 h12 hzero
    have heK : ψ (l₁ - l₂) ∈ K := by
      dsimp [K]
      exact z36_mem_zmultiples_of_addOrderOf_eq_three hrorder heorder
    have heker : ψ (l₁ - l₂) ∈ kernelFinset q := by
      apply (mem_kernelFinset q _).2
      rw [show q.ker = K by exact QuotientAddGroup.ker_mk' K]
      exact heK
    have hc₁ : ψ l₁ ∈ C := (mem_preimageFinset ψ C l₁).mp hl₁
    have hc₂ : ψ l₂ ∈ C := (mem_preimageFinset ψ C l₂).mp hl₂
    have hcne : ψ l₁ ≠ ψ l₂ := by
      intro heq
      have hz : ψ (l₁ - l₂) = 0 := by
        rw [map_sub, heq, sub_self]
      have hone : addOrderOf (ψ (l₁ - l₂)) = 1 :=
        AddMonoid.addOrderOf_eq_one_iff.mpr hz
      omega
    exact (sub_not_mem_kernelFinset_of_tiles hKC hc₁ hc₂ hcne)
      (by simpa only [map_sub] using heker)
  refine ⟨L, cyclotomicSpectrum_of_tiles_of_complement_nonzero
    hTiles hA ?_ hnonzero⟩
  exact hcard.trans hLcard.symm

/-- Every twelve-point tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_twelve
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 12) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨C, hTiles36, hprojectionCard⟩ :=
    z180_tile_descends_to_z36_of_five_not_dvd_card hTiles (by omega)
  have hprojectionCard12 : (A.image z180TileProjection36).card = 12 :=
    hprojectionCard.trans hcard
  obtain ⟨L, hSpectrum36⟩ :=
    z36_exists_spectrum_of_tile_card_twelve hTiles36 hprojectionCard12
  have hFourier36 : FourierSpectrum (A.image z180TileProjection36) L :=
    (cyclotomicSpectrum_iff_fourierSpectrum _ _).mp hSpectrum36
  have hprojectionInj : Set.InjOn z180TileProjection36 A := by
    apply Finset.card_image_iff.mp
    exact hprojectionCard
  let L180 : Finset (ZMod 180) := L.image z36ScaleFive
  refine ⟨L180, (cyclotomicSpectrum_iff_fourierSpectrum _ _).mpr ?_⟩
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · calc
      A.card = (A.image z180TileProjection36).card := hprojectionCard.symm
      _ = L.card := hFourier36.2.1
      _ = L180.card := by
        symm
        exact Finset.card_image_of_injective L z36ScaleFive_injective
  · intro l₁ hl₁ l₂ hl₂ hlne
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₁)
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₂)
    have hdne : d₁ ≠ d₂ := by
      intro h
      subst d₂
      exact hlne rfl
    rw [← map_sub]
    rw [← fourierSum_image_projection36 A (d₁ - d₂) hprojectionInj]
    exact hFourier36.2.2 d₁ hd₁ d₂ hd₂ hdne

#print axioms z36_exists_spectrum_of_tile_card_twelve
#print axioms z180_exists_spectrum_of_tile_card_twelve

end Fuglede
