import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

/-!
# Exact finite tilings

The definition in this file is deliberately independent of Fourier analysis.
`Tiles A B` says that the addition map from `A × B` to the ambient finite
group is a bijection.  Thus it encodes both existence and uniqueness of every
representation `g = a + b`.
-/

namespace Fuglede

variable {G : Type*} [Add G]

/-- The addition map whose bijectivity is the finite-group tiling condition. -/
def sumMap (A B : Finset G) : ↑(A ×ˢ B) → G :=
  fun p => p.1.1 + p.1.2

/-- `A` tiles `G` with complement `B` if every element has exactly one
representation as `a + b`. -/
def Tiles (A B : Finset G) : Prop :=
  Function.Bijective (sumMap A B)

instance [DecidableEq G] [Fintype G] (A B : Finset G) : Decidable (Tiles A B) :=
  by
    classical
    unfold Tiles Function.Bijective Function.Injective Function.Surjective
    infer_instance

/-- The elementary cardinality obstruction for a finite tiling. -/
theorem card_mul_eq_card_of_tiles [Fintype G] {A B : Finset G}
    (h : Tiles A B) : A.card * B.card = Fintype.card G := by
  let e : ↑(A ×ˢ B) ≃ G := Equiv.ofBijective (sumMap A B) h
  have hc := Fintype.card_congr e
  simpa using hc

end Fuglede
