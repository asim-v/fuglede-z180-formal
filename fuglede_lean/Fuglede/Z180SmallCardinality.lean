import Fuglede.FourierTiling
import Fuglede.ProjectionLift
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Small spectral sets in `ZMod 180`

This file proves the cardinality-two and cardinality-three cases of
spectral-implies-tiling in `ZMod 180`.  The proof is structural: orthogonality
maps the set onto a translate of a subgroup of order two or three, and a
tiling of that image is lifted through the corresponding character quotient.
-/

namespace Fuglede

open scoped ComplexConjugate

section TilingUtilities

variable {G H : Type*}
variable [AddCommGroup G] [AddCommGroup H]
variable [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H]

/-- In an abelian group, the two factors of a tiling may be interchanged. -/
theorem tiles_comm {A B : Finset G} (h : Tiles A B) : Tiles B A := by
  constructor
  · intro x y hxy
    let sx : ↑(A ×ˢ B) := ⟨(x.1.2, x.1.1), by
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp x.2).2, (Finset.mem_product.mp x.2).1⟩⟩
    let sy : ↑(A ×ˢ B) := ⟨(y.1.2, y.1.1), by
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp y.2).2, (Finset.mem_product.mp y.2).1⟩⟩
    have hs : sx = sy := h.1 (by
      simpa [sx, sy, sumMap, add_comm] using hxy)
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => z.1.2) hs) (congrArg (fun z => z.1.1) hs)
  · intro g
    rcases h.2 g with ⟨x, hx⟩
    refine ⟨⟨(x.1.2, x.1.1), ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp x.2).2, (Finset.mem_product.mp x.2).1⟩
    · simpa [sumMap, add_comm] using hx

/-- Translation of the first factor preserves an exact tiling. -/
theorem tiles_translate_left (g : G) {A B : Finset G} (h : Tiles A B) :
    Tiles (A.image fun a => g + a) B := by
  constructor
  · intro x y hxy
    rcases Finset.mem_image.mp (Finset.mem_product.mp x.2).1 with ⟨a, ha, hax⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp y.2).1 with ⟨a', ha', hay⟩
    have hb := (Finset.mem_product.mp x.2).2
    have hb' := (Finset.mem_product.mp y.2).2
    let sx : ↑(A ×ˢ B) := ⟨(a, x.1.2), Finset.mem_product.mpr ⟨ha, hb⟩⟩
    let sy : ↑(A ×ˢ B) := ⟨(a', y.1.2), Finset.mem_product.mpr ⟨ha', hb'⟩⟩
    have hsums : sumMap A B sx = sumMap A B sy := by
      simp only [sumMap, sx, sy]
      have hxy' := hxy
      simp only [sumMap] at hxy'
      rw [← hax, ← hay] at hxy'
      have hc : a + x.1.2 = a' + y.1.2 := by
        apply add_left_cancel (a := g)
        simpa [add_assoc] using hxy'
      exact hc
    have hs : sx = sy := h.1 hsums
    have haa : a = a' :=
      congrArg (fun z : ↑(A ×ˢ B) => z.1.1) hs
    have hbb : x.1.2 = y.1.2 :=
      congrArg (fun z : ↑(A ×ˢ B) => z.1.2) hs
    apply Subtype.ext
    apply Prod.ext
    · rw [← hax, ← hay, haa]
    · exact hbb
  · intro x
    rcases h.2 (x - g) with ⟨y, hy⟩
    refine ⟨⟨(g + y.1.1, y.1.2), ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨y.1.1,
        (Finset.mem_product.mp y.2).1, rfl⟩, (Finset.mem_product.mp y.2).2⟩
    · simpa [sumMap, add_assoc] using congrArg (fun z => g + z) hy

/-- Every kernel of a surjective map of finite abelian groups has a finite
transversal, hence tiles the domain. -/
theorem exists_kernel_tiling_complement (φ : G →+ H)
    (hφ : Function.Surjective φ) :
    ∃ C : Finset G, Tiles (kernelFinset φ) C := by
  classical
  rcases hφ.hasRightInverse with ⟨s, hs⟩
  let C : Finset G := Finset.univ.image s
  have hs_inj : Function.Injective s := hs.injective
  have hcard : C.card = Fintype.card H := by
    simp [C, Finset.card_image_of_injective _ hs_inj]
  have hinj : Set.InjOn φ (C : Set G) := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨u, -, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v, -, rfl⟩
    have huv : u = v := by
      rw [hs u, hs v] at hxy
      exact hxy
    subst v
    rfl
  have hCK : Tiles C (kernelFinset φ) := by
    apply transversal_tiles_kernel φ C
    · exact (kernel_difference_free_iff_injOn φ C).2 hinj
    · exact hcard
  exact ⟨C, tiles_comm hCK⟩

/-- The finset used for a kernel has the same cardinality as the kernel
subgroup itself. -/
def kernelFinsetEquivKer (φ : G →+ H) :
    ↑(kernelFinset φ) ≃ φ.ker where
  toFun x := ⟨x.1, (mem_kernelFinset φ x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_kernelFinset φ x.1).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_kernelFinset_quotient_zmultiples (t : G) :
    (kernelFinset (QuotientAddGroup.mk' (AddSubgroup.zmultiples t))).card =
      addOrderOf t := by
  let K : AddSubgroup G := AddSubgroup.zmultiples t
  let q : G →+ G ⧸ K := QuotientAddGroup.mk' K
  calc
    (kernelFinset q).card = Fintype.card ↑(kernelFinset q) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card q.ker := Fintype.card_congr (kernelFinsetEquivKer q)
    _ = Nat.card q.ker := Nat.card_eq_fintype_card.symm
    _ = Nat.card K := by rw [show q.ker = K by exact QuotientAddGroup.ker_mk' K]
    _ = addOrderOf t := Nat.card_zmultiples t

/-- If a finite set maps injectively and its image is a translate of a
cyclic subgroup, it tiles. -/
theorem tiles_of_image_eq_translate_zmultiples
    (φ : G →+ H) (hφ : Function.Surjective φ)
    (A : Finset G) (g t : H)
    (hinj : Set.InjOn φ (A : Set G))
    (himage : A.image φ =
      (kernelFinset
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples t))).image
          (fun x => g + x)) :
    ∃ B : Finset G, Tiles A B := by
  let K : AddSubgroup H := AddSubgroup.zmultiples t
  let q : H →+ H ⧸ K := QuotientAddGroup.mk' K
  rcases exists_kernel_tiling_complement q
      (QuotientAddGroup.mk'_surjective K) with ⟨C, hKC⟩
  have htranslated :
      Tiles ((kernelFinset q).image fun x => g + x) C :=
    tiles_translate_left g hKC
  have himageTiles : Tiles (A.image φ) C := by
    rw [himage]
    exact htranslated
  exact ⟨preimageFinset φ C,
    lift_tiles_of_surjective φ hφ A C hinj himageTiles⟩

theorem pair_image_structure (φ : G →+ H) (a b : G)
    (horder : addOrderOf (φ a - φ b) = 2) :
    Set.InjOn φ (({a, b} : Finset G) : Set G) ∧
      ({a, b} : Finset G).image φ =
        (kernelFinset (QuotientAddGroup.mk'
          (AddSubgroup.zmultiples (φ a - φ b)))).image
            (fun x => φ b + x) := by
  let t : H := φ a - φ b
  have horder_t : addOrderOf t = 2 := by simpa [t] using horder
  have htne : t ≠ 0 := by
    intro ht0
    have : addOrderOf t = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr ht0
    rw [horder_t] at this
    norm_num at this
  have habφ : φ a ≠ φ b := by
    intro hab
    apply htne
    simp [t, hab]
  have hinj : Set.InjOn φ (({a, b} : Finset G) : Set G) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact (habφ hxy).elim
    · exact (habφ hxy.symm).elim
    · rfl
  refine ⟨hinj, ?_⟩
  let Kfin : Finset H := kernelFinset
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples t))
  have htmem : t ∈ Kfin := by
    apply (mem_kernelFinset _ t).2
    rw [QuotientAddGroup.ker_mk']
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have hzeromem : (0 : H) ∈ Kfin := by simp [Kfin]
  have hsubset : ({a, b} : Finset G).image φ ⊆
      Kfin.image (fun x => φ b + x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · apply Finset.mem_image.mpr
      refine ⟨t, htmem, ?_⟩
      simp [t]
    · apply Finset.mem_image.mpr
      exact ⟨0, hzeromem, by simp⟩
  apply Finset.eq_of_subset_of_card_le hsubset
  have hleft : (({a, b} : Finset G).image φ).card = 2 := by
    rw [Finset.card_image_iff.mpr hinj]
    simp [show a ≠ b by
      intro hab
      subst b
      exact habφ rfl]
  have hright : (Kfin.image (fun x => φ b + x)).card = 2 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
    change (kernelFinset (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (φ a - φ b)))).card = 2
    rw [card_kernelFinset_quotient_zmultiples, horder]
  omega

theorem triple_image_structure (φ : G →+ H) (a b c : G)
    (horder : addOrderOf (φ a - φ b) = 3)
    (hcstep : φ c - φ a = φ a - φ b) :
    Set.InjOn φ (({a, b, c} : Finset G) : Set G) ∧
      ({a, b, c} : Finset G).image φ =
        (kernelFinset (QuotientAddGroup.mk'
          (AddSubgroup.zmultiples (φ a - φ b)))).image
            (fun x => φ b + x) := by
  let t : H := φ a - φ b
  have horder_t : addOrderOf t = 3 := by simpa [t] using horder
  have htne : t ≠ 0 := by
    intro ht0
    have : addOrderOf t = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr ht0
    rw [horder_t] at this
    norm_num at this
  have ht3 : 3 • t = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [horder_t]
  have habφ : φ a ≠ φ b := by
    intro hab
    apply htne
    simp [t, hab]
  have hcaφ : φ c ≠ φ a := by
    intro hca
    apply htne
    dsimp [t]
    rw [← hcstep]
    simp [hca]
  have hcbφ : φ c ≠ φ b := by
    intro hcb
    have ht2 : 2 • t = 0 := by
      rw [two_nsmul]
      calc
        t + t = (φ c - φ a) + t :=
          congrArg (fun z => z + t) (by simpa [t] using hcstep.symm)
        _ = 0 := by simp [hcb, t]
    apply htne
    have ht3' := ht3
    rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul] at ht3'
    have : 2 • t + t = 0 := ht3'
    simpa [ht2] using this
  have hinj : Set.InjOn φ (({a, b, c} : Finset G) : Set G) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl
    · rfl
    · exact (habφ hxy).elim
    · exact (hcaφ hxy.symm).elim
    · exact (habφ hxy.symm).elim
    · rfl
    · exact (hcbφ hxy.symm).elim
    · exact (hcaφ hxy).elim
    · exact (hcbφ hxy).elim
    · rfl
  refine ⟨hinj, ?_⟩
  let Kfin : Finset H := kernelFinset
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples t))
  have htmem : t ∈ Kfin := by
    apply (mem_kernelFinset _ t).2
    rw [QuotientAddGroup.ker_mk']
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have ht2mem : (2 • t) ∈ Kfin := by
    apply (mem_kernelFinset _ (2 • t)).2
    rw [QuotientAddGroup.ker_mk']
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(2 : ℤ), by
      simpa only [ofNat_zsmul]⟩
  have hzeromem : (0 : H) ∈ Kfin := by simp [Kfin]
  have hast : φ a = φ b + t := by simp [t]
  have hcst : φ c = φ b + 2 • t := by
    have hca : φ c = φ a + t := by
      calc
        φ c = (φ c - φ a) + φ a := by abel
        _ = t + φ a := by rw [hcstep]
        _ = φ a + t := add_comm _ _
    rw [hca, hast, two_nsmul]
    abel
  have hsubset : ({a, b, c} : Finset G).image φ ⊆
      Kfin.image (fun x => φ b + x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨t, htmem, hast.symm⟩
    · exact Finset.mem_image.mpr ⟨0, hzeromem, by simp⟩
    · exact Finset.mem_image.mpr ⟨2 • t, ht2mem, hcst.symm⟩
  apply Finset.eq_of_subset_of_card_le hsubset
  have hleft : (({a, b, c} : Finset G).image φ).card = 3 := by
    rw [Finset.card_image_iff.mpr hinj]
    simp [show a ≠ b by intro h; subst b; exact habφ rfl,
      show a ≠ c by intro h; subst c; exact hcaφ rfl,
      show b ≠ c by intro h; subst c; exact hcbφ rfl]
  have hright : (Kfin.image (fun x => φ b + x)).card = 3 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
    change (kernelFinset (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (φ a - φ b)))).card = 3
    rw [card_kernelFinset_quotient_zmultiples, horder]
  omega

end TilingUtilities

section CharacterGeometry

/-- Two unit complex numbers summing to zero have a nontrivial quotient of
order two. -/
theorem unit_pair_ratio_order_two {u v : ℂ}
    (hu : u * star u = 1) (hv : v * star v = 1)
    (hzero : u + v = 0) :
    (u * star v) ^ 2 = 1 ∧ u * star v ≠ 1 := by
  have huv : u = -v := by linear_combination hzero
  have hratio : u * star v = -1 := by
    rw [huv, neg_mul, hv]
  constructor
  · rw [hratio]
    norm_num
  · rw [hratio]
    norm_num

/-- Three unit complex numbers summing to zero have pairwise quotients that
are nontrivial cube roots of unity. -/
theorem unit_triple_ratio_order_three {u v w : ℂ}
    (hu : u * star u = 1) (hv : v * star v = 1)
    (hw : w * star w = 1)
    (hzero : u + v + w = 0) :
    (u * star v) ^ 3 = 1 ∧ u * star v ≠ 1 ∧
      w * star u = u * star v := by
  let x : ℂ := u * (starRingEnd ℂ) v
  let y : ℂ := v * (starRingEnd ℂ) u
  have hu' : u * (starRingEnd ℂ) u = 1 := hu
  have hv' : v * (starRingEnd ℂ) v = 1 := hv
  have hw' :
      (u + v) * ((starRingEnd ℂ) u + (starRingEnd ℂ) v) = 1 := by
    have hwu : w = -(u + v) := by linear_combination hzero
    have hwcopy := hw
    change w * (starRingEnd ℂ) w = 1 at hwcopy
    rw [hwu] at hwcopy
    rw [map_neg, map_add] at hwcopy
    ring_nf at hwcopy ⊢
    exact hwcopy
  have hxy_sum : x + y + 1 = 0 := by
    dsimp [x, y]
    linear_combination hw' - hu' - hv'
  have hxy_mul : x * y = 1 := by
    dsimp [x, y]
    calc
      (u * (starRingEnd ℂ) v) * (v * (starRingEnd ℂ) u) =
          (u * (starRingEnd ℂ) u) * (v * (starRingEnd ℂ) v) := by ring
      _ = 1 := by rw [hu', hv', one_mul]
  have hxquad : x ^ 2 + x + 1 = 0 := by
    linear_combination x * hxy_sum - hxy_mul
  refine ⟨?_, ?_, ?_⟩
  · have : x ^ 3 - 1 = 0 := by
      calc
        x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
        _ = 0 := by rw [hxquad, mul_zero]
    exact sub_eq_zero.mp this
  · intro hx1
    have hx1' : x = 1 := by simpa [x] using hx1
    rw [hx1'] at hxy_mul hxy_sum
    have hy1 : y = 1 := by simpa using hxy_mul
    rw [hy1] at hxy_sum
    norm_num at hxy_sum
  · have hwu : w = -(u + v) := by linear_combination hzero
    have hgoal :
        w * (starRingEnd ℂ) u = u * (starRingEnd ℂ) v := by
      dsimp [x, y] at hxy_sum
      calc
        w * (starRingEnd ℂ) u =
            -(u + v) * (starRingEnd ℂ) u := by rw [hwu]
        _ = -(u * (starRingEnd ℂ) u) -
            v * (starRingEnd ℂ) u := by ring
        _ = -1 - v * (starRingEnd ℂ) u := by rw [hu']
        _ = u * (starRingEnd ℂ) v := by linear_combination -hxy_sum
    exact hgoal

end CharacterGeometry

section Z180Phase

/-- Multiplication by a frequency, viewed as an additive homomorphism. -/
def z180MulHom (d : ZMod 180) : ZMod 180 →+ ZMod 180 where
  toFun x := x * d
  map_zero' := by simp
  map_add' x y := by ring

/-- The same map with its codomain restricted to its range. -/
def z180PhaseHom (d : ZMod 180) :
    ZMod 180 →+ (z180MulHom d).range :=
  (z180MulHom d).rangeRestrict

@[simp]
theorem coe_z180PhaseHom (d x : ZMod 180) :
    ((z180PhaseHom d x : (z180MulHom d).range) : ZMod 180) = x * d := rfl

theorem z180_char_unit (x : ZMod 180) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  simp

theorem z180_char_ratio (a b d : ZMod 180) :
    ZMod.stdAddChar (a * d) * star (ZMod.stdAddChar (b * d)) =
      ZMod.stdAddChar ((a - b) * d) := by
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem z180_pair_phase_order_two {a b d : ZMod 180}
    (hzero : ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) = 0) :
    addOrderOf (z180PhaseHom d a - z180PhaseHom d b) = 2 := by
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  have hgeom := unit_pair_ratio_order_two
    (z180_char_unit (a * d)) (z180_char_unit (b * d)) hzero
  let z : ZMod 180 := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z := by
    exact z180_char_ratio a b d
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
  let t := z180PhaseHom d a - z180PhaseHom d b
  have htcoe : (t.1 : ZMod 180) = z := by
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

theorem z180_triple_phase_structure {a b c d : ZMod 180}
    (hzero : ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) +
      ZMod.stdAddChar (c * d) = 0) :
    addOrderOf (z180PhaseHom d a - z180PhaseHom d b) = 3 ∧
      z180PhaseHom d c - z180PhaseHom d a =
        z180PhaseHom d a - z180PhaseHom d b := by
  let u : ℂ := ZMod.stdAddChar (a * d)
  let v : ℂ := ZMod.stdAddChar (b * d)
  let w : ℂ := ZMod.stdAddChar (c * d)
  have hgeom := unit_triple_ratio_order_three
    (z180_char_unit (a * d)) (z180_char_unit (b * d))
    (z180_char_unit (c * d)) hzero
  let z : ZMod 180 := (a - b) * d
  have hratio : u * star v = ZMod.stdAddChar z := by
    exact z180_char_ratio a b d
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
  let t := z180PhaseHom d a - z180PhaseHom d b
  have htcoe : (t.1 : ZMod 180) = z := by
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
    rw [← z180_char_ratio c a d, ← z180_char_ratio a b d]
    exact hgeom.2.2
  convert hcRatio using 1 <;> ring

end Z180Phase

section Z180SmallCases

/-- Every spectral two-point subset of `ZMod 180` tiles. -/
theorem z180_spectral_card_two_tiles {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 2) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp hcard
  have hLcard : L.card = 2 := by
    rw [← hSpec.2.1]
    exact hcard
  obtain ⟨l₁, l₂, hlne, hLeq⟩ := Finset.card_eq_two.mp hLcard
  have hl₁ : l₁ ∈ L := by rw [hLeq]; simp
  have hl₂ : l₂ ∈ L := by rw [hLeq]; simp
  let d : ZMod 180 := l₁ - l₂
  have hcyclo : CyclotomicZero 180 A d :=
    hSpec.2.2 l₁ hl₁ l₂ hl₂ hlne
  have hfourier : fourierSum A d = 0 :=
    (cyclotomicZero_iff_fourierSum_zero A d).1 hcyclo
  rw [fourierSum_eq_finset_sum] at hfourier
  have hzero :
      ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) = 0 := by
    simpa [hAeq, hab] using hfourier
  let φ := z180PhaseHom d
  have horder : addOrderOf (φ a - φ b) = 2 :=
    z180_pair_phase_order_two hzero
  have hstructure := pair_image_structure φ a b horder
  have hinj : Set.InjOn φ (A : Set (ZMod 180)) := by
    simpa [hAeq] using hstructure.1
  have himage : A.image φ =
      (kernelFinset (QuotientAddGroup.mk'
        (AddSubgroup.zmultiples (φ a - φ b)))).image
          (fun x => φ b + x) := by
    rw [hAeq]
    exact hstructure.2
  exact tiles_of_image_eq_translate_zmultiples φ
    (AddMonoidHom.rangeRestrict_surjective (z180MulHom d)) A
    (φ b) (φ a - φ b) hinj himage

/-- Every spectral three-point subset of `ZMod 180` tiles. -/
theorem z180_spectral_card_three_tiles {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 3) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  obtain ⟨a, b, c, hab, hac, hbc, hAeq⟩ :=
    Finset.card_eq_three.mp hcard
  have hLcard : L.card = 3 := by
    rw [← hSpec.2.1]
    exact hcard
  obtain ⟨l₁, l₂, l₃, hl12, hl13, hl23, hLeq⟩ :=
    Finset.card_eq_three.mp hLcard
  have hl₁ : l₁ ∈ L := by rw [hLeq]; simp
  have hl₂ : l₂ ∈ L := by rw [hLeq]; simp
  let d : ZMod 180 := l₁ - l₂
  have hcyclo : CyclotomicZero 180 A d :=
    hSpec.2.2 l₁ hl₁ l₂ hl₂ hl12
  have hfourier : fourierSum A d = 0 :=
    (cyclotomicZero_iff_fourierSum_zero A d).1 hcyclo
  rw [fourierSum_eq_finset_sum] at hfourier
  have hzero :
      ZMod.stdAddChar (a * d) + ZMod.stdAddChar (b * d) +
        ZMod.stdAddChar (c * d) = 0 := by
    simpa [hAeq, hab, hac, hbc, add_assoc] using hfourier
  let φ := z180PhaseHom d
  have hphase := z180_triple_phase_structure hzero
  have hstructure := triple_image_structure φ a b c hphase.1 hphase.2
  have hinj : Set.InjOn φ (A : Set (ZMod 180)) := by
    simpa [hAeq] using hstructure.1
  have himage : A.image φ =
      (kernelFinset (QuotientAddGroup.mk'
        (AddSubgroup.zmultiples (φ a - φ b)))).image
          (fun x => φ b + x) := by
    rw [hAeq]
    exact hstructure.2
  exact tiles_of_image_eq_translate_zmultiples φ
    (AddMonoidHom.rangeRestrict_surjective (z180MulHom d)) A
    (φ b) (φ a - φ b) hinj himage

end Z180SmallCases

end Fuglede
