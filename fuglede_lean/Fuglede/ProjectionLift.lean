import Fuglede.ProjectionTiling

/-!
# Lifting tilings through finite additive quotients

A tiling in a surjective homomorphic image lifts to the original finite
additive group when the first factor has no projection collisions.  This is
the modulus-independent descent endpoint used by the `ZMod 180` proof and by
the proposed prime-layer reduction principle.
-/

namespace Fuglede

section ProjectionLift

variable {G H : Type*}
variable [AddCommGroup G] [AddCommGroup H]
variable [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H]

/-- A concrete finset model for the inverse image of a finite set. -/
def preimageFinset (φ : G →+ H) (C : Finset H) : Finset G :=
  Finset.univ.filter fun g => φ g ∈ C

omit [Fintype H] [DecidableEq G] in
@[simp]
theorem mem_preimageFinset (φ : G →+ H) (C : Finset H) (g : G) :
    g ∈ preimageFinset φ C ↔ φ g ∈ C := by
  simp [preimageFinset]

/-- A tiling of the image of the first factor lifts provided that factor has
no collisions under the homomorphism.  Surjectivity is not needed: it is
already forced on the relevant sums by the tiling of `A.image φ`. -/
theorem lift_tiles_of_image (φ : G →+ H) (A : Finset G) (C : Finset H)
    (hinj : Set.InjOn φ (A : Set G))
    (himage : Tiles (A.image φ) C) :
    Tiles A (preimageFinset φ C) := by
  constructor
  · intro x y hxy
    have hax := (Finset.mem_product.mp x.2).1
    have hbx := (Finset.mem_product.mp x.2).2
    have hay := (Finset.mem_product.mp y.2).1
    have hby := (Finset.mem_product.mp y.2).2
    let ix : ↑((A.image φ) ×ˢ C) :=
      ⟨(φ x.1.1, φ x.1.2), Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨x.1.1, hax, rfl⟩,
          (mem_preimageFinset φ C x.1.2).1 hbx⟩⟩
    let iy : ↑((A.image φ) ×ˢ C) :=
      ⟨(φ y.1.1, φ y.1.2), Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨y.1.1, hay, rfl⟩,
          (mem_preimageFinset φ C y.1.2).1 hby⟩⟩
    have hi : ix = iy := himage.1 (by
      simpa [ix, iy, sumMap, map_add] using congrArg φ hxy)
    have hipair : ix.1 = iy.1 := congrArg Subtype.val hi
    have hφa : φ x.1.1 = φ y.1.1 := congrArg Prod.fst hipair
    have haeq : x.1.1 = y.1.1 := hinj hax hay hφa
    have hbeq : x.1.2 = y.1.2 := by
      have hxy' := hxy
      simp only [sumMap] at hxy'
      rw [haeq] at hxy'
      exact add_left_cancel hxy'
    exact Subtype.ext (Prod.ext haeq hbeq)
  · intro g
    rcases himage.2 (φ g) with ⟨y, hy⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp y.2).1 with
      ⟨a, ha, hay⟩
    let b : G := g - a
    have hb : b ∈ preimageFinset φ C := by
      apply (mem_preimageFinset φ C b).2
      have hc := (Finset.mem_product.mp y.2).2
      have hbmap : φ b = y.1.2 := by
        simpa [b, sumMap, hay] using congrArg (fun z => z - φ a) hy.symm
      rw [hbmap]
      exact hc
    refine ⟨⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩, ?_⟩
    simp [sumMap, b]

/-- Backwards-compatible quotient spelling.  The surjectivity hypothesis is
useful when constructing the image tiling, although the lifting step itself
only needs `lift_tiles_of_image`. -/
theorem lift_tiles_of_surjective (φ : G →+ H)
    (_hφ : Function.Surjective φ) (A : Finset G) (C : Finset H)
    (hinj : Set.InjOn φ (A : Set G))
    (himage : Tiles (A.image φ) C) :
    Tiles A (preimageFinset φ C) :=
  lift_tiles_of_image φ A C hinj himage

end ProjectionLift

end Fuglede
