import Fuglede.Z180SmallCardinality
import Fuglede.Z180TilingSpectralReduction
import Mathlib.Tactic

/-!
# Large tiles with prime-size complements in `ZMod 180`

The first case is a tile of size ninety.  Its two-point complement has a
nonzero Fourier zero.  The corresponding order-two phase element defines a
two-element subgroup; a transversal to that subgroup pulls back to a
ninety-point frequency set on which the complement Fourier transform never
vanishes.  The tiling zero-cover identity then makes that frequency set a
spectrum for the original tile.
-/

namespace Fuglede

/-- The unique nonzero solution of `2x = 0` in `ZMod 180` is `90`. -/
theorem z180_eq_ninety_of_two_nsmul_eq_zero {x : ZMod 180}
    (htwo : 2 • x = 0) (hxne : x ≠ 0) : x = 90 := by
  have hcast : ((2 * x.val : ℕ) : ZMod 180) = 0 := by
    calc
      ((2 * x.val : ℕ) : ZMod 180) = (2 : ZMod 180) * x := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        norm_num
      _ = 2 • x := by simp
      _ = 0 := htwo
  have hdiv : 180 ∣ 2 * x.val :=
    (ZMod.natCast_eq_zero_iff (2 * x.val) 180).mp hcast
  have hxpos : 0 < x.val := by
    exact Nat.pos_of_ne_zero (by
      intro h
      apply hxne
      apply ZMod.val_injective
      simpa [h])
  have hxlt : x.val < 180 := ZMod.val_lt x
  obtain ⟨k, hk⟩ := hdiv
  have hxval : x.val = 90 := by omega
  calc
    x = (x.val : ZMod 180) := (ZMod.natCast_zmod_val x).symm
    _ = 90 := by
      rw [hxval]
      norm_num

/-- The unique nonzero element of additive order two in `ZMod 180` is `90`. -/
theorem z180_eq_ninety_of_addOrderOf_eq_two {x : ZMod 180}
    (horder : addOrderOf x = 2) : x = 90 := by
  apply z180_eq_ninety_of_two_nsmul_eq_zero
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [horder]
  · intro hx
    subst x
    simp at horder

/-- Two different elements of the second factor of a tiling by `{0,r}`
cannot differ by `r`. -/
theorem sub_ne_of_pair_tiles {H : Type*} [AddCommGroup H]
    [Fintype H] [DecidableEq H] {r x y : H} {C : Finset H}
    (hr : r ≠ 0) (hTiles : Tiles ({0, r} : Finset H) C)
    (hx : x ∈ C) (hy : y ∈ C) : x - y ≠ r := by
  intro hdiff
  let p : ↥(({0, r} : Finset H) ×ˢ C) := ⟨(0, x), by simp [hx]⟩
  let q : ↥(({0, r} : Finset H) ×ˢ C) := ⟨(r, y), by simp [hy]⟩
  have hpq : sumMap ({0, r} : Finset H) C p =
      sumMap ({0, r} : Finset H) C q := by
    simp only [sumMap, p, q, zero_add]
    rw [sub_eq_iff_eq_add] at hdiff
    exact hdiff
  have heq := hTiles.1 hpq
  have hfirst : (0 : H) = r := congrArg (fun z => z.1.1) heq
  exact hr hfirst.symm

/-- A transversal to a kernel has no nonzero difference in that kernel. -/
theorem sub_not_mem_kernelFinset_of_tiles {G Q : Type*}
    [AddCommGroup G] [AddCommGroup Q] [Fintype G] [Fintype Q]
    [DecidableEq G] [DecidableEq Q] {q : G →+ Q} {C : Finset G}
    (hTiles : Tiles (kernelFinset q) C) {x y : G}
    (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    x - y ∉ kernelFinset q := by
  intro hxy
  let p : ↥(kernelFinset q ×ˢ C) := ⟨(0, x), by simp [hx]⟩
  let r : ↥(kernelFinset q ×ˢ C) := ⟨(x - y, y),
    Finset.mem_product.mpr ⟨hxy, hy⟩⟩
  have hsum : sumMap (kernelFinset q) C p =
      sumMap (kernelFinset q) C r := by
    simp [sumMap, p, r]
  have hpr := hTiles.1 hsum
  have hzero : (0 : G) = x - y := congrArg (fun z => z.1.1) hpr
  exact hne (sub_eq_zero.mp hzero.symm)

/-- A tiling zero cover turns any frequency set avoiding zeros of the
complement into a spectrum. -/
theorem cyclotomicSpectrum_of_tiles_of_complement_nonzero
    {N : ℕ} [NeZero N] {A B L : Finset (ZMod N)}
    (hTiles : Tiles A B) (hA : A.Nonempty) (hcard : A.card = L.card)
    (hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum B (l₁ - l₂) ≠ 0) :
    CyclotomicSpectrum N A L := by
  apply (cyclotomicSpectrum_iff_fourierSpectrum A L).2
  refine ⟨hA, hcard, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hne
  exact (fourier_zero_cover_of_tiles hTiles (l₁ - l₂)
    (sub_ne_zero.mpr hne)).resolve_right (hnonzero l₁ hl₁ l₂ hl₂ hne)

/-- A two-point Fourier zero gives an order-two value for the phase map whose
parameter is the point difference. -/
theorem z180_pair_zero_phase_order_two
    {b₀ b₁ d : ZMod 180} (hb : b₀ ≠ b₁)
    (hzero : fourierSum ({b₀, b₁} : Finset (ZMod 180)) d = 0) :
    addOrderOf ((z180PhaseHom (b₀ - b₁)) d) = 2 := by
  have hsum :
      ZMod.stdAddChar (b₀ * d) + ZMod.stdAddChar (b₁ * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [hb] using hzero
  let s := z180PhaseHom d b₀ - z180PhaseHom d b₁
  let r := z180PhaseHom (b₀ - b₁) d
  have hsorder : addOrderOf s = 2 := z180_pair_phase_order_two hsum
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

/-- A three-point Fourier zero gives an order-three value for the phase map
whose parameter is the difference of the first two points. -/
theorem z180_triple_zero_phase_order_three
    {b₀ b₁ b₂ d : ZMod 180} (h01 : b₀ ≠ b₁) (h02 : b₀ ≠ b₂)
    (h12 : b₁ ≠ b₂)
    (hzero : fourierSum ({b₀, b₁, b₂} : Finset (ZMod 180)) d = 0) :
    addOrderOf ((z180PhaseHom (b₀ - b₁)) d) = 3 := by
  have hsum :
      ZMod.stdAddChar (b₀ * d) + ZMod.stdAddChar (b₁ * d) +
        ZMod.stdAddChar (b₂ * d) = 0 := by
    rw [fourierSum_eq_finset_sum] at hzero
    simpa [h01, h02, h12, add_assoc] using hzero
  let s := z180PhaseHom d b₀ - z180PhaseHom d b₁
  let r := z180PhaseHom (b₀ - b₁) d
  have hsorder : addOrderOf s = 3 := (z180_triple_phase_structure hsum).1
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

/-- The nonzero solutions of `3x = 0` in `ZMod 180` are `60` and `120`. -/
theorem z180_eq_sixty_or_oneTwenty_of_three_nsmul_eq_zero {x : ZMod 180}
    (hthree : 3 • x = 0) (hxne : x ≠ 0) : x = 60 ∨ x = 120 := by
  have hcast : ((3 * x.val : ℕ) : ZMod 180) = 0 := by
    calc
      ((3 * x.val : ℕ) : ZMod 180) = (3 : ZMod 180) * x := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        norm_num
      _ = 3 • x := by simp
      _ = 0 := hthree
  have hdiv : 180 ∣ 3 * x.val :=
    (ZMod.natCast_eq_zero_iff (3 * x.val) 180).mp hcast
  have hxpos : 0 < x.val := by
    exact Nat.pos_of_ne_zero (by
      intro h
      apply hxne
      apply ZMod.val_injective
      simpa [h])
  have hxlt : x.val < 180 := ZMod.val_lt x
  obtain ⟨k, hk⟩ := hdiv
  have hxval : x.val = 60 ∨ x.val = 120 := by omega
  rcases hxval with hxval | hxval
  · left
    calc
      x = (x.val : ZMod 180) := (ZMod.natCast_zmod_val x).symm
      _ = 60 := by rw [hxval]; norm_num
  · right
    calc
      x = (x.val : ZMod 180) := (ZMod.natCast_zmod_val x).symm
      _ = 120 := by rw [hxval]; norm_num

/-- In a subgroup of `ZMod 180`, every order-three element belongs to the
cyclic subgroup generated by any other order-three element. -/
theorem mem_zmultiples_of_addOrderOf_eq_three
    {H : AddSubgroup (ZMod 180)} {r e : H}
    (hr : addOrderOf r = 3) (he : addOrderOf e = 3) :
    e ∈ AddSubgroup.zmultiples r := by
  have hrthree : 3 • r.1 = (0 : ZMod 180) :=
    congrArg Subtype.val
      (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hr]))
  have hethree : 3 • e.1 = (0 : ZMod 180) :=
    congrArg Subtype.val
      (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [he]))
  have hrne : r.1 ≠ (0 : ZMod 180) := by
    intro h
    have hz : r = 0 := Subtype.ext h
    have hone : addOrderOf r = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hz
    omega
  have hene : e.1 ≠ (0 : ZMod 180) := by
    intro h
    have hz : e = 0 := Subtype.ext h
    have hone : addOrderOf e = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hz
    omega
  rcases z180_eq_sixty_or_oneTwenty_of_three_nsmul_eq_zero hrthree hrne with
    hr60 | hr120 <;>
  rcases z180_eq_sixty_or_oneTwenty_of_three_nsmul_eq_zero hethree hene with
    he60 | he120
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨1, ?_⟩
    simpa using Subtype.ext (he60.trans hr60.symm).symm
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨2, Subtype.ext ?_⟩
    change (2 : ℤ) • r.1 = e.1
    rw [he120, hr60]
    decide
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨2, Subtype.ext ?_⟩
    change (2 : ℤ) • r.1 = e.1
    rw [he60, hr120]
    decide
  · apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨1, ?_⟩
    simpa using Subtype.ext (he120.trans hr120.symm).symm

/-- Every ninety-point tile in `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_ninety
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 90) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
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
  let t : ZMod 180 := b₀ - b₁
  let H := (z180MulHom t).range
  let ψ : ZMod 180 →+ H := z180PhaseHom t
  let r : H := ψ d₀
  have hrorder : addOrderOf r = 2 := by
    dsimp [r, ψ, t]
    exact z180_pair_zero_phase_order_two hb hBzero
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
      rw [hkcard]
      rw [Finset.card_pair hrne.symm]
  have hpairTiles : Tiles ({0, r} : Finset H) C := by
    rw [← hkernel]
    exact hKC
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (z180MulHom t).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective (z180MulHom t)
  have himage : ({0, d₀} : Finset (ZMod 180)).image ψ = {0, r} := by
    simp [r]
  have hinj : Set.InjOn ψ (({0, d₀} : Finset (ZMod 180)) : Set (ZMod 180)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exfalso
      apply hrne
      simpa [r] using hxy.symm
    · exfalso
      apply hrne
      simpa [r] using hxy
    · rfl
  let L : Finset (ZMod 180) := preimageFinset ψ C
  have hsmallTiles : Tiles ({0, d₀} : Finset (ZMod 180)) L := by
    dsimp [L]
    apply lift_tiles_of_surjective ψ hψsurj ({0, d₀} : Finset (ZMod 180)) C hinj
    rw [himage]
    exact hpairTiles
  have hLcard : L.card = 90 := by
    have hpaircard : ({0, d₀} : Finset (ZMod 180)).card = 2 := by
      exact Finset.card_pair hd₀.symm
    have hc : 2 * L.card = 180 := by
      simpa [hpaircard] using card_mul_eq_card_of_tiles hsmallTiles
    omega
  have hrval : r.1 = (90 : ZMod 180) := by
    apply z180_eq_ninety_of_two_nsmul_eq_zero
    · exact congrArg Subtype.val
        (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hrorder]))
    · intro h
      apply hrne
      apply Subtype.ext
      exact h
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum ({b₀, b₁} : Finset (ZMod 180)) (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hne hzero
    have heorder : addOrderOf (ψ (l₁ - l₂)) = 2 := by
      dsimp [ψ, t]
      exact z180_pair_zero_phase_order_two hb hzero
    have heval : (ψ (l₁ - l₂)).1 = (90 : ZMod 180) := by
      apply z180_eq_ninety_of_two_nsmul_eq_zero
      · exact congrArg Subtype.val
          (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [heorder]))
      · intro h
        have hz : ψ (l₁ - l₂) = 0 := Subtype.ext h
        have hone : addOrderOf (ψ (l₁ - l₂)) = 1 :=
          AddMonoid.addOrderOf_eq_one_iff.mpr hz
        omega
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

/-- Every sixty-point tile in `ZMod 180` is spectral.  The proof pulls back a
transversal to the order-three phase subgroup determined by its three-point
tiling complement. -/
theorem z180_exists_spectrum_of_tile_card_sixty
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 60) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
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
  let t : ZMod 180 := b₀ - b₁
  let H := (z180MulHom t).range
  let ψ : ZMod 180 →+ H := z180PhaseHom t
  let r : H := ψ d₀ - ψ 0
  have hrorder : addOrderOf r = 3 := by
    dsimp [r]
    simpa [ψ, t] using
      z180_triple_zero_phase_order_three h01 h02 h12 hBzero
  let K : AddSubgroup H := AddSubgroup.zmultiples r
  let q : H →+ H ⧸ K := QuotientAddGroup.mk' K
  obtain ⟨C, hKC⟩ := exists_kernel_tiling_complement q
    (QuotientAddGroup.mk'_surjective K)
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (z180MulHom t).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective (z180MulHom t)
  have hstep : ψ (2 • d₀) - ψ d₀ = ψ d₀ - ψ 0 := by
    apply Subtype.ext
    change (2 • d₀) * t - d₀ * t = d₀ * t - 0 * t
    simp [two_nsmul]
    ring
  have hphaseorder : addOrderOf (ψ d₀ - ψ 0) = 3 := by
    exact hrorder
  have hstructure := triple_image_structure ψ d₀ 0 (2 • d₀) hphaseorder hstep
  have hinj : Set.InjOn ψ
      (({d₀, 0, 2 • d₀} : Finset (ZMod 180)) : Set (ZMod 180)) :=
    hstructure.1
  have himage :
      ({d₀, 0, 2 • d₀} : Finset (ZMod 180)).image ψ = kernelFinset q := by
    rw [hstructure.2]
    change (kernelFinset q).image (fun x => ψ 0 + x) = kernelFinset q
    simp
  let L : Finset (ZMod 180) := preimageFinset ψ C
  have hsmallTiles : Tiles ({d₀, 0, 2 • d₀} : Finset (ZMod 180)) L := by
    dsimp [L]
    apply lift_tiles_of_surjective ψ hψsurj
      ({d₀, 0, 2 • d₀} : Finset (ZMod 180)) C hinj
    rw [himage]
    exact hKC
  have hkcard : (kernelFinset q).card = 3 := by
    change (kernelFinset (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples r))).card = 3
    rw [card_kernelFinset_quotient_zmultiples, hrorder]
  have hDcard : ({d₀, 0, 2 • d₀} : Finset (ZMod 180)).card = 3 := by
    calc
      ({d₀, 0, 2 • d₀} : Finset (ZMod 180)).card =
          (({d₀, 0, 2 • d₀} : Finset (ZMod 180)).image ψ).card :=
        (Finset.card_image_iff.mpr hinj).symm
      _ = (kernelFinset q).card := congrArg Finset.card himage
      _ = 3 := hkcard
  have hLcard : L.card = 60 := by
    have hc := card_mul_eq_card_of_tiles hsmallTiles
    rw [hDcard] at hc
    have hc' : 3 * L.card = 180 := by simpa using hc
    omega
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum ({b₀, b₁, b₂} : Finset (ZMod 180)) (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hne hzero
    have heorder : addOrderOf (ψ (l₁ - l₂)) = 3 := by
      dsimp [ψ, t]
      exact z180_triple_zero_phase_order_three h01 h02 h12 hzero
    have heK : ψ (l₁ - l₂) ∈ K := by
      dsimp [K]
      exact mem_zmultiples_of_addOrderOf_eq_three hrorder heorder
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

#print axioms z180_exists_spectrum_of_tile_card_ninety
#print axioms z180_exists_spectrum_of_tile_card_sixty

end Fuglede
