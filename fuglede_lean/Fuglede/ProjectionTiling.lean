import Fuglede.FiniteTiling
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.EquivFin

/-!
# Tiling from a complete set of representatives

Let `φ : G →+ H` be a homomorphism of finite additive groups.  If no two
distinct elements of `A` differ by an element of `ker φ`, then `φ` is
injective on `A`.  When `A` has the same cardinality as `H`, its restriction
to `A` is therefore a bijection.  This makes `A` a complete set of
representatives for the cosets of `ker φ`, and hence `A` tiles `G` with
`ker φ`.  In particular, surjectivity of `φ` follows from these hypotheses
and need not be assumed separately.

This is the purely finite-group endpoint needed to turn a projection
obstruction into an exact tiling statement.
-/

namespace Fuglede

section ProjectionTiling

variable {G H : Type*}
variable [AddGroup G] [AddGroup H]
variable [Fintype G] [Fintype H]
variable [DecidableEq G] [DecidableEq H]

/-- The kernel of `φ`, represented as a finset in its finite domain. -/
def kernelFinset (φ : G →+ H) : Finset G :=
  Finset.univ.filter fun g => φ g = 0

omit [Fintype H] [DecidableEq G] in
@[simp]
theorem mem_kernelFinset (φ : G →+ H) (g : G) :
    g ∈ kernelFinset φ ↔ g ∈ φ.ker := by
  simp [kernelFinset, AddMonoidHom.mem_ker]

omit [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] in
/-- Two elements have the same image under an additive homomorphism exactly
when their difference belongs to its kernel. -/
theorem sub_mem_ker_iff_map_eq (φ : G →+ H) (a b : G) :
    a - b ∈ φ.ker ↔ φ a = φ b := by
  simp [sub_eq_zero]

omit [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] in
/-- The useful finite-set form of "no nonzero difference lies in the kernel":
it is precisely injectivity of the projection on `A`. -/
theorem kernel_difference_free_iff_injOn (φ : G →+ H) (A : Finset G) :
    (∀ a ∈ A, ∀ b ∈ A, a - b ∈ φ.ker → a = b) ↔
      Set.InjOn φ (A : Set G) := by
  constructor
  · intro h a ha b hb hab
    exact h a ha b hb ((sub_mem_ker_iff_map_eq φ a b).2 hab)
  · intro h a ha b hb hab
    exact h ha hb ((sub_mem_ker_iff_map_eq φ a b).1 hab)

omit [Fintype G] [DecidableEq G] [DecidableEq H] in
/-- An injective restriction between finite types of the same cardinality is
bijective.  Here the domain is the subtype cut out by the finset `A`. -/
theorem restricted_map_bijective_of_card_eq (φ : G →+ H) (A : Finset G)
    (hinj : Set.InjOn φ (A : Set G))
    (hcard : A.card = Fintype.card H) :
    Function.Bijective (fun a : (A : Set G) => φ a.1) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b hab
    apply Subtype.ext
    exact hinj a.2 b.2 hab
  · simpa using hcard

omit [DecidableEq G] in
/-- A complete collection of representatives for the fibres of an additive
homomorphism tiles the domain by the kernel.  The hypotheses already force
the homomorphism to be surjective. -/
theorem transversal_tiles_kernel (φ : G →+ H) (A : Finset G)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a - b ∈ φ.ker → a = b)
    (hcard : A.card = Fintype.card H) :
    Tiles A (kernelFinset φ) := by
  have hinj : Set.InjOn φ (A : Set G) :=
    (kernel_difference_free_iff_injOn φ A).1 hdiff
  have hbij : Function.Bijective (fun a : (A : Set G) => φ a.1) :=
    restricted_map_bijective_of_card_eq φ A hinj hcard
  constructor
  · intro x y hxy
    rcases x with ⟨⟨a, k⟩, hx⟩
    rcases y with ⟨⟨b, l⟩, hy⟩
    have ha : a ∈ A := (Finset.mem_product.mp hx).1
    have hk : k ∈ kernelFinset φ := (Finset.mem_product.mp hx).2
    have hb : b ∈ A := (Finset.mem_product.mp hy).1
    have hl : l ∈ kernelFinset φ := (Finset.mem_product.mp hy).2
    simp only [sumMap] at hxy
    have hk0 : φ k = 0 := by
      exact (AddMonoidHom.mem_ker.mp ((mem_kernelFinset φ k).1 hk))
    have hl0 : φ l = 0 := by
      exact (AddMonoidHom.mem_ker.mp ((mem_kernelFinset φ l).1 hl))
    have habmap : φ a = φ b := by
      have := congrArg φ hxy
      simpa [map_add, hk0, hl0] using this
    have hab : a = b := hinj ha hb habmap
    subst b
    have hkl : k = l := by
      simpa using add_left_cancel hxy
    subst l
    rfl
  · intro g
    rcases hbij.2 (φ g) with ⟨a, haφ⟩
    let k : G := -a.1 + g
    have hk : k ∈ kernelFinset φ := by
      apply (mem_kernelFinset φ k).2
      apply AddMonoidHom.mem_ker.mpr
      simp [k, haφ]
    refine ⟨⟨(a.1, k), Finset.mem_product.mpr ⟨a.2, hk⟩⟩, ?_⟩
    simp [sumMap, k]

end ProjectionTiling

end Fuglede
