import Fuglede.FiniteTiling
import Mathlib.Data.Finset.Prod

/-!
# The combinatorial endpoint of the cardinality-eleven argument

For `G = H × ZMod 11`, the Fourier argument shows that a spectral set of
cardinality eleven has exactly one point above every element of `ZMod 11`.
Such a transversal is the graph of a function `f : ZMod 11 → H`.  This file
checks, for arbitrary finite additive groups, that every such graph tiles with
the horizontal subgroup `H × {0}`.

The Fourier/dimension argument forcing the graph structure is documented in
`FUGLEDE_2310_SIZE11.md`; it is not yet formalized here.
-/

namespace Fuglede

section GraphTiling

variable {H P : Type*}
variable [AddGroup H] [AddGroup P]
variable [Fintype H] [Fintype P]
variable [DecidableEq H] [DecidableEq P]

/-- The graph of a function between finite additive groups. -/
def graphFinset (f : P → H) : Finset (H × P) :=
  Finset.univ.image fun p => (f p, p)

/-- The horizontal subgroup, represented as a finset. -/
def horizontalFinset : Finset (H × P) :=
  Finset.univ.image fun h => (h, 0)

@[simp]
theorem mem_graphFinset (f : P → H) (h : H) (p : P) :
    (h, p) ∈ graphFinset f ↔ h = f p := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨q, -, hq⟩
    have hp : q = p := congrArg Prod.snd hq
    subst hp
    exact (congrArg Prod.fst hq).symm
  · intro hh
    subst hh
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩

@[simp]
theorem mem_horizontalFinset (h : H) (p : P) :
    (h, p) ∈ (horizontalFinset : Finset (H × P)) ↔ p = 0 := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨k, -, hk⟩
    exact (congrArg Prod.snd hk).symm
  · intro hp
    subst hp
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩

/-- A graph has an explicit exact tiling complement: the horizontal subgroup.
For `(h,p)`, the unique representation is
`(f p,p) + (-f p + h,0)`. -/
theorem graphFinset_tiles_horizontal (f : P → H) :
    Tiles (graphFinset f) (horizontalFinset : Finset (H × P)) := by
  constructor
  · intro x y hxy
    rcases x with ⟨⟨a, b⟩, hxab⟩
    rcases y with ⟨⟨c, d⟩, hycd⟩
    simp only [Finset.mem_product] at hxab hycd
    rcases a with ⟨ah, ap⟩
    rcases b with ⟨bh, bp⟩
    rcases c with ⟨ch, cp⟩
    rcases d with ⟨dh, dp⟩
    have hah : ah = f ap := (mem_graphFinset f ah ap).mp hxab.1
    have hbp : bp = 0 := (mem_horizontalFinset bh bp).mp hxab.2
    have hch : ch = f cp := (mem_graphFinset f ch cp).mp hycd.1
    have hdp : dp = 0 := (mem_horizontalFinset dh dp).mp hycd.2
    simp only [sumMap, Prod.fst_add, Prod.snd_add] at hxy
    have hapcp : ap = cp := by
      simpa [hbp, hdp] using congrArg Prod.snd hxy
    subst cp
    have hbhdh : bh = dh := by
      simpa [hah, hch] using congrArg Prod.fst hxy
    subst dh
    subst hah
    subst hch
    subst hbp
    subst hdp
    rfl
  · intro g
    let a : H × P := (f g.2, g.2)
    let b : H × P := (-f g.2 + g.1, 0)
    have ha : a ∈ graphFinset f := by
      simp [a]
    have hb : b ∈ (horizontalFinset : Finset (H × P)) := by
      simp [b]
    refine ⟨⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩, ?_⟩
    apply Prod.ext
    · simp [sumMap, a, b]
    · simp [sumMap, a, b]

end GraphTiling

section ElevenArithmetic

theorem eleven_does_not_dvd_210 : ¬ 11 ∣ 210 := by decide

theorem eleven_dvd_2310 : 11 ∣ 2310 := by decide

end ElevenArithmetic

end Fuglede
