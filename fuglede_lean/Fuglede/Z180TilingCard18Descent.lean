import Fuglede.Z180TilingModFiveDescent

/-! # The cardinality-eighteen tiling-to-spectral case -/

namespace Fuglede

def z36MulHom (d : ZMod 36) : ZMod 36 →+ ZMod 36 where
  toFun x := x * d
  map_zero' := by simp
  map_add' x y := by ring

def z36PhaseHom (d : ZMod 36) : ZMod 36 →+ (z36MulHom d).range :=
  (z36MulHom d).rangeRestrict

@[simp]
theorem coe_z36PhaseHom (d x : ZMod 36) :
    ((z36PhaseHom d x : (z36MulHom d).range) : ZMod 36) = x * d := rfl

private theorem z36_char_unit (x : ZMod 36) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

private theorem z36_char_ratio (a b d : ZMod 36) :
    ZMod.stdAddChar (a * d) * star (ZMod.stdAddChar (b * d)) =
      ZMod.stdAddChar ((a - b) * d) := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem z36_pair_phase_order_two {a b d : ZMod 36}
    (hzero : ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) = 0) :
    addOrderOf (z36PhaseHom d a - z36PhaseHom d b) = 2 := by
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  have hgeom := unit_pair_ratio_order_two
    (z36_char_unit (a * d)) (z36_char_unit (b * d)) hzero
  let z : ZMod 36 := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z := z36_char_ratio a b d
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
  let t := z36PhaseHom d a - z36PhaseHom d b
  have htcoe : (t.1 : ZMod 36) = z := by
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

private theorem z36_pair_zero_phase_order_two
    {b₀ b₁ d : ZMod 36} (hb : b₀ ≠ b₁)
    (hzero : fourierSum ({b₀, b₁} : Finset (ZMod 36)) d = 0) :
    addOrderOf ((z36PhaseHom (b₀ - b₁)) d) = 2 := by
  have hsum :
      ZMod.stdAddChar (b₀ * d) + ZMod.stdAddChar (b₁ * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [hb] using hzero
  let s := z36PhaseHom d b₀ - z36PhaseHom d b₁
  let r := z36PhaseHom (b₀ - b₁) d
  have hsorder : addOrderOf s = 2 := z36_pair_phase_order_two hsum
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

private theorem z36_eq_eighteen_of_addOrderOf_eq_two {x : ZMod 36}
    (horder : addOrderOf x = 2) : x = 18 := by
  rw [← ZMod.natCast_zmod_val x] at horder ⊢
  rw [ZMod.addOrderOf_coe x.val (by norm_num)] at horder
  have hlt := x.val_lt
  interval_cases x.val <;> norm_num at horder <;> simp_all

private theorem z36_coe_addOrderOf_eq_two
    {H : AddSubgroup (ZMod 36)} {x : H}
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

/-- Every eighteen-point tile of `ZMod 36` is spectral. -/
theorem z36_exists_spectrum_of_tile_card_eighteen
    {A B : Finset (ZMod 36)} (hTiles : Tiles A B)
    (hcard : A.card = 18) :
    ∃ L : Finset (ZMod 36), CyclotomicSpectrum 36 A L := by
  have hprod : A.card * B.card = 36 := by
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
  let t : ZMod 36 := b₀ - b₁
  let H := (z36MulHom t).range
  let ψ : ZMod 36 →+ H := z36PhaseHom t
  let r : H := ψ d₀
  have hrorder : addOrderOf r = 2 := by
    dsimp [r, ψ, t]
    exact z36_pair_zero_phase_order_two hb hBzero
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
    change Function.Surjective (z36MulHom t).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective (z36MulHom t)
  have himage : ({0, d₀} : Finset (ZMod 36)).image ψ = {0, r} := by
    simp [r]
  have hinj : Set.InjOn ψ (({0, d₀} : Finset (ZMod 36)) : Set (ZMod 36)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exfalso; apply hrne; simpa [r] using hxy.symm
    · exfalso; apply hrne; simpa [r] using hxy
    · rfl
  let L : Finset (ZMod 36) := preimageFinset ψ C
  have hsmallTiles : Tiles ({0, d₀} : Finset (ZMod 36)) L := by
    dsimp [L]
    apply lift_tiles_of_surjective ψ hψsurj ({0, d₀} : Finset (ZMod 36)) C hinj
    rw [himage]
    exact hpairTiles
  have hLcard : L.card = 18 := by
    have hpaircard : ({0, d₀} : Finset (ZMod 36)).card = 2 :=
      Finset.card_pair hd₀.symm
    have hc : 2 * L.card = 36 := by
      simpa [hpaircard] using card_mul_eq_card_of_tiles hsmallTiles
    omega
  have hrval : r.1 = (18 : ZMod 36) := by
    exact z36_eq_eighteen_of_addOrderOf_eq_two
      (z36_coe_addOrderOf_eq_two hrorder)
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum ({b₀, b₁} : Finset (ZMod 36)) (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hne hzero
    have heorder : addOrderOf (ψ (l₁ - l₂)) = 2 := by
      dsimp [ψ, t]
      exact z36_pair_zero_phase_order_two hb hzero
    have heval : (ψ (l₁ - l₂)).1 = (18 : ZMod 36) :=
      z36_eq_eighteen_of_addOrderOf_eq_two
        (z36_coe_addOrderOf_eq_two heorder)
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

/-- Every eighteen-point tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_eighteen
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 18) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨C, hTiles36, hprojectionCard⟩ :=
    z180_tile_descends_to_z36_of_five_not_dvd_card hTiles (by omega)
  have hprojectionCard18 : (A.image z180TileProjection36).card = 18 :=
    hprojectionCard.trans hcard
  obtain ⟨L, hSpectrum36⟩ :=
    z36_exists_spectrum_of_tile_card_eighteen hTiles36 hprojectionCard18
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

#print axioms z36_exists_spectrum_of_tile_card_eighteen
#print axioms z180_exists_spectrum_of_tile_card_eighteen

end Fuglede
