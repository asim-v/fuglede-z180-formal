import Fuglede.Z180K30Fibres
import Mathlib.Tactic

/-!
# Reassembling five common fibre tilings at cardinality thirty

Under the Chinese remainder identification `ZMod 180 ≃ ZMod 5 × ZMod 36`,
the complement used below lives entirely in the second coordinate.  Hence a
single complement which tiles every fifth-coordinate fibre tiles the original
set in `ZMod 180`.
-/

namespace Fuglede

/-- Lift a complement in `ZMod 36` into the zero fifth-coordinate slice of
`ZMod 180`. -/
noncomputable def z180K30LiftComplement
    (B : Finset (ZMod 36)) : Finset (ZMod 180) :=
  B.image fun b => z180K30CRT.symm ((0 : ZMod 5), b)

/-- A common exact complement for all five projected fibres gives an exact
tiling of the original set. -/
theorem z180_k30_tiles_of_common_fibre_complement
    (A : Finset (ZMod 180)) (B : Finset (ZMod 36))
    (htiles : ∀ c : ZMod 5, Tiles (z180K30Fibre A c) B) :
    Tiles A (z180K30LiftComplement B) := by
  constructor
  · rintro ⟨⟨ax, bx⟩, hx⟩ ⟨⟨ay, by0⟩, hy⟩ hsum
    obtain ⟨hax, hbx⟩ := Finset.mem_product.mp hx
    obtain ⟨hay, hby⟩ := Finset.mem_product.mp hy
    obtain ⟨bx36, hbx36, rfl⟩ := Finset.mem_image.mp hbx
    obtain ⟨by36, hby36, rfl⟩ := Finset.mem_image.mp hby
    have hsum' :
        ax + z180K30CRT.symm ((0 : ZMod 5), bx36) =
          ay + z180K30CRT.symm ((0 : ZMod 5), by36) := by
      simpa only [sumMap] using hsum
    have hfirst :
        (ZMod.cast ax : ZMod 5) = (ZMod.cast ay : ZMod 5) := by
      have h := congrArg (fun z => (z180K30CRT z).1) hsum'
      simpa [map_add, z180K30CRT_apply] using h
    have hsecond :
        (ZMod.cast ax : ZMod 36) + bx36 =
          (ZMod.cast ay : ZMod 36) + by36 := by
      have h := congrArg (fun z => (z180K30CRT z).2) hsum'
      simpa [map_add, z180K30CRT_apply] using h
    have haxF :
        (ZMod.cast ax : ZMod 36) ∈
          z180K30Fibre A (ZMod.cast ax : ZMod 5) := by
      exact Finset.mem_image.mpr ⟨ax,
        Finset.mem_filter.mpr ⟨hax, rfl⟩, rfl⟩
    have hayF :
        (ZMod.cast ay : ZMod 36) ∈
          z180K30Fibre A (ZMod.cast ax : ZMod 5) := by
      exact Finset.mem_image.mpr ⟨ay,
        Finset.mem_filter.mpr ⟨hay, hfirst.symm⟩, rfl⟩
    let px : ↑(z180K30Fibre A (ZMod.cast ax : ZMod 5) ×ˢ B) :=
      ⟨((ZMod.cast ax : ZMod 36), bx36),
        Finset.mem_product.mpr ⟨haxF, hbx36⟩⟩
    let py : ↑(z180K30Fibre A (ZMod.cast ax : ZMod 5) ×ˢ B) :=
      ⟨((ZMod.cast ay : ZMod 36), by36),
        Finset.mem_product.mpr ⟨hayF, hby36⟩⟩
    have hp : px = py := (htiles (ZMod.cast ax : ZMod 5)).1 (by
      simpa only [px, py, sumMap] using hsecond)
    have hax36 : (ZMod.cast ax : ZMod 36) = (ZMod.cast ay : ZMod 36) :=
      congrArg (fun p => p.1.1) hp
    have hb36 : bx36 = by36 := congrArg (fun p => p.1.2) hp
    have haxy : ax = ay := by
      apply z180K30CRT.injective
      rw [z180K30CRT_apply, z180K30CRT_apply]
      exact Prod.ext hfirst hax36
    apply Subtype.ext
    exact Prod.ext haxy (congrArg (fun b =>
      z180K30CRT.symm ((0 : ZMod 5), b)) hb36)
  · intro g
    let c : ZMod 5 := ZMod.cast g
    obtain ⟨p, hp⟩ := (htiles c).2 (ZMod.cast g : ZMod 36)
    rcases p with ⟨⟨a36, b36⟩, hpMem⟩
    obtain ⟨ha36, hb36⟩ := Finset.mem_product.mp hpMem
    obtain ⟨a, haFilter, haa36⟩ := Finset.mem_image.mp ha36
    obtain ⟨ha, hac⟩ := Finset.mem_filter.mp haFilter
    have hp' : a36 + b36 = (ZMod.cast g : ZMod 36) := by
      simpa only [sumMap] using hp
    refine ⟨⟨(a, z180K30CRT.symm ((0 : ZMod 5), b36)), ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr ⟨ha,
        Finset.mem_image.mpr ⟨b36, hb36, rfl⟩⟩
    · simp only [sumMap]
      apply z180K30CRT.injective
      rw [map_add, z180K30CRT.apply_symm_apply, z180K30CRT_apply,
        z180K30CRT_apply]
      apply Prod.ext
      · simpa [map_add, c] using hac
      · simpa [map_add, haa36] using hp'

#print axioms z180_k30_tiles_of_common_fibre_complement

end Fuglede
