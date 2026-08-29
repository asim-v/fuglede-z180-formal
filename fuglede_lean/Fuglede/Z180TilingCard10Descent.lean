import Fuglede.Z180TilingModNineDescent

/-! # The cardinality-ten tiling-to-spectral case -/

namespace Fuglede

def z20MulHom (d : ZMod 20) : ZMod 20 →+ ZMod 20 where
  toFun x := x * d
  map_zero' := by simp
  map_add' x y := by ring

def z20PhaseHom (d : ZMod 20) : ZMod 20 →+ (z20MulHom d).range :=
  (z20MulHom d).rangeRestrict

private theorem z20_char_unit (x : ZMod 20) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

private theorem z20_char_ratio (a b d : ZMod 20) :
    ZMod.stdAddChar (a * d) * star (ZMod.stdAddChar (b * d)) =
      ZMod.stdAddChar ((a - b) * d) := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem z20_pair_phase_order_two {a b d : ZMod 20}
    (hzero : ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) = 0) :
    addOrderOf (z20PhaseHom d a - z20PhaseHom d b) = 2 := by
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  have hgeom := unit_pair_ratio_order_two
    (z20_char_unit (a * d)) (z20_char_unit (b * d)) hzero
  let z : ZMod 20 := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z := z20_char_ratio a b d
  have hzpow : (ZMod.stdAddChar z) ^ 2 = 1 := by
    rw [← hratio]
    exact hgeom.1
  have hzne : z ≠ 0 := by
    intro hz
    apply hgeom.2
    rw [hratio, hz, AddChar.map_zero_eq_one]
  have hzsmul : 2 • z = 0 := by
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_nsmul_eq_pow, hzpow, AddChar.map_zero_eq_one]
  let t := z20PhaseHom d a - z20PhaseHom d b
  have htcoe : (t.1 : ZMod 20) = z := by
    change a * d - b * d = (a - b) * d
    ring
  have htne : t ≠ 0 := by
    intro ht0
    apply hzne
    rw [← htcoe]
    exact congrArg Subtype.val ht0
  have htsmul : 2 • t = 0 := by
    apply Subtype.ext
    simpa [htcoe] using hzsmul
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime htsmul htne

private theorem z20_pair_zero_phase_order_two
    {b₀ b₁ d : ZMod 20} (hb : b₀ ≠ b₁)
    (hzero : fourierSum ({b₀, b₁} : Finset (ZMod 20)) d = 0) :
    addOrderOf ((z20PhaseHom (b₀ - b₁)) d) = 2 := by
  have hsum :
      ZMod.stdAddChar (b₀ * d) + ZMod.stdAddChar (b₁ * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [hb] using hzero
  let s := z20PhaseHom d b₀ - z20PhaseHom d b₁
  let r := z20PhaseHom (b₀ - b₁) d
  have hsorder : addOrderOf s = 2 := z20_pair_phase_order_two hsum
  have hstwo : 2 • s = 0 := by
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
  have hrtwo : 2 • r = 0 := by
    apply Subtype.ext
    change 2 • r.1 = 0
    rw [← hcoe]
    exact congrArg Subtype.val hstwo
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime hrtwo hrne

private theorem z20_eq_ten_of_addOrderOf_eq_two {x : ZMod 20}
    (horder : addOrderOf x = 2) : x = 10 := by
  rw [← ZMod.natCast_zmod_val x] at horder ⊢
  rw [ZMod.addOrderOf_coe x.val (by norm_num)] at horder
  have hlt := x.val_lt
  interval_cases x.val <;> norm_num at horder <;> simp_all

private theorem z20_coe_addOrderOf_eq_two
    {H : AddSubgroup (ZMod 20)} {x : H}
    (horder : addOrderOf x = 2) : addOrderOf x.1 = 2 := by
  have htwo : 2 • x = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [horder]
  have hxne : x ≠ 0 := by
    intro hx
    have hone : addOrderOf x = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hx
    omega
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply addOrderOf_eq_prime
  · exact congrArg Subtype.val htwo
  · intro hx
    apply hxne
    exact Subtype.ext hx

/-- Every ten-point tile of `ZMod 20` is spectral. -/
theorem z20_exists_spectrum_of_tile_card_ten
    {A B : Finset (ZMod 20)} (hTiles : Tiles A B)
    (hcard : A.card = 10) :
    ∃ L : Finset (ZMod 20), CyclotomicSpectrum 20 A L := by
  have hprod : A.card * B.card = 20 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 2 := by omega
  obtain ⟨b₀, b₁, hb, rfl⟩ := Finset.card_eq_two.mp hBcard
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hAproper : A ≠ Finset.univ := by
    intro h
    subst A
    simp at hcard
  obtain ⟨d₀, hd₀, hBzero⟩ :=
    exists_nonzero_fourier_zero_left_of_tiles (tiles_comm hTiles) hA hAproper
  let t : ZMod 20 := b₀ - b₁
  let H := (z20MulHom t).range
  let ψ : ZMod 20 →+ H := z20PhaseHom t
  let r : H := ψ d₀
  have hrorder : addOrderOf r = 2 := by
    dsimp [r, ψ, t]
    exact z20_pair_zero_phase_order_two hb hBzero
  have hrne : r ≠ 0 := by
    intro hr
    have hone : addOrderOf r = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hr
    omega
  let K : AddSubgroup H := AddSubgroup.zmultiples r
  let q : H →+ H ⧸ K := QuotientAddGroup.mk' K
  obtain ⟨C, hKC⟩ := exists_kernel_tiling_complement q
    (QuotientAddGroup.mk'_surjective K)
  have hrmem : r ∈ kernelFinset q := by
    apply (mem_kernelFinset q r).2
    rw [show q.ker = K by exact QuotientAddGroup.ker_mk' K]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have hkernel : kernelFinset q = ({0, r} : Finset H) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      · rw [Finset.mem_singleton.mp hx]
        exact hrmem
    · have hkcard : (kernelFinset q).card = 2 := by
        change (kernelFinset (QuotientAddGroup.mk'
          (AddSubgroup.zmultiples r))).card = 2
        rw [card_kernelFinset_quotient_zmultiples, hrorder]
      rw [hkcard, Finset.card_pair hrne.symm]
  have hpairTiles : Tiles ({0, r} : Finset H) C := by
    rw [← hkernel]
    exact hKC
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (z20MulHom t).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective (z20MulHom t)
  have himage : ({0, d₀} : Finset (ZMod 20)).image ψ = {0, r} := by
    simp [r]
  have hinj : Set.InjOn ψ (({0, d₀} : Finset (ZMod 20)) : Set (ZMod 20)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exfalso; apply hrne; simpa [r] using hxy.symm
    · exfalso; apply hrne; simpa [r] using hxy
    · rfl
  let L : Finset (ZMod 20) := preimageFinset ψ C
  have hsmallTiles : Tiles ({0, d₀} : Finset (ZMod 20)) L := by
    dsimp [L]
    apply lift_tiles_of_surjective ψ hψsurj ({0, d₀} : Finset (ZMod 20)) C hinj
    rw [himage]
    exact hpairTiles
  have hLcard : L.card = 10 := by
    have hpaircard : ({0, d₀} : Finset (ZMod 20)).card = 2 :=
      Finset.card_pair hd₀.symm
    have hc : 2 * L.card = 20 := by
      simpa [hpaircard] using card_mul_eq_card_of_tiles hsmallTiles
    omega
  have hrval : r.1 = (10 : ZMod 20) := by
    exact z20_eq_ten_of_addOrderOf_eq_two
      (z20_coe_addOrderOf_eq_two hrorder)
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum ({b₀, b₁} : Finset (ZMod 20)) (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hne hzero
    have heorder : addOrderOf (ψ (l₁ - l₂)) = 2 := by
      dsimp [ψ, t]
      exact z20_pair_zero_phase_order_two hb hzero
    have heval : (ψ (l₁ - l₂)).1 = (10 : ZMod 20) :=
      z20_eq_ten_of_addOrderOf_eq_two
        (z20_coe_addOrderOf_eq_two heorder)
    have heqr : ψ (l₁ - l₂) = r := by
      apply Subtype.ext
      exact heval.trans hrval.symm
    have hc₁ : ψ l₁ ∈ C := (mem_preimageFinset ψ C l₁).mp hl₁
    have hc₂ : ψ l₂ ∈ C := (mem_preimageFinset ψ C l₂).mp hl₂
    apply sub_ne_of_pair_tiles hrne hpairTiles hc₁ hc₂
    simpa only [map_sub] using heqr
  refine ⟨L, cyclotomicSpectrum_of_tiles_of_complement_nonzero
    hTiles hA ?_ hnonzero⟩
  exact hcard.trans hLcard.symm

/-- Every ten-point tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_ten
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 10) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨C, hTiles20, hprojectionCard⟩ :=
    z180_tile_descends_to_z20_of_three_not_dvd_card hTiles (by omega)
  have hprojectionCard10 : (A.image z180TileProjection20).card = 10 :=
    hprojectionCard.trans hcard
  obtain ⟨L, hSpectrum20⟩ :=
    z20_exists_spectrum_of_tile_card_ten hTiles20 hprojectionCard10
  have hFourier20 : FourierSpectrum (A.image z180TileProjection20) L :=
    (cyclotomicSpectrum_iff_fourierSpectrum _ _).mp hSpectrum20
  have hprojectionInj : Set.InjOn z180TileProjection20 A := by
    apply Finset.card_image_iff.mp
    exact hprojectionCard
  let L180 : Finset (ZMod 180) := L.image z20ScaleNine
  refine ⟨L180, (cyclotomicSpectrum_iff_fourierSpectrum _ _).mpr ?_⟩
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · calc
      A.card = (A.image z180TileProjection20).card := hprojectionCard.symm
      _ = L.card := hFourier20.2.1
      _ = L180.card := by
        symm
        exact Finset.card_image_of_injective L z20ScaleNine_injective
  · intro l₁ hl₁ l₂ hl₂ hlne
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₁)
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₂)
    have hdne : d₁ ≠ d₂ := by
      intro h
      subst d₂
      exact hlne rfl
    rw [← map_sub]
    rw [← fourierSum_image_projection20 A (d₁ - d₂) hprojectionInj]
    exact hFourier20.2.2 d₁ hd₁ d₂ hd₂ hdne

#print axioms z20_exists_spectrum_of_tile_card_ten
#print axioms z180_exists_spectrum_of_tile_card_ten

end Fuglede
