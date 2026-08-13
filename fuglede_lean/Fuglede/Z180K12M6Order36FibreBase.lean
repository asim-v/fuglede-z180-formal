import Mathlib.Tactic

namespace Fuglede

inductive Z180K12Order36Fibre
  | zero
  | balancedOne
  | balancedTwo
  | balancedThree
  | positive
  | negative
  deriving DecidableEq, Fintype

def Z180K12Order36Fibre.even : Z180K12Order36Fibre → Int
  | .zero => 0
  | .balancedOne => 1
  | .balancedTwo => 2
  | .balancedThree => 3
  | .positive => 3
  | .negative => 0

def Z180K12Order36Fibre.odd : Z180K12Order36Fibre → Int
  | .zero => 0
  | .balancedOne => 1
  | .balancedTwo => 2
  | .balancedThree => 3
  | .positive => 0
  | .negative => 3

def z180K12Order36DecidableForall
    {p : Z180K12Order36Fibre → Prop}
    (hp : ∀ f, Decidable (p f)) : Decidable (∀ f, p f) :=
  @Fintype.decidableForallFintype Z180K12Order36Fibre p hp inferInstance

def Z180K12Order36TableProperty
    (f0 f1 f2 f3 f4 f5 : Z180K12Order36Fibre) : Prop :=
  f0.even + f2.odd + f4.even = 3 →
  f1.even + f3.odd + f5.even = 3 →
  f0.odd + f2.even + f4.odd = 3 →
  f1.odd + f3.even + f5.odd = 3 →
  ((f0.even + f0.odd) - (f2.even + f2.odd) -
      (f3.even + f3.odd) + (f5.even + f5.odd)) % 5 = 0 →
  ((f1.even + f1.odd) + (f2.even + f2.odd) -
      (f4.even + f4.odd) - (f5.even + f5.odd)) % 5 = 0 →
  (f0.even + f0.odd) - (f2.even + f2.odd) -
      (f3.even + f3.odd) + (f5.even + f5.odd) = 0 ∧
    (f1.even + f1.odd) + (f2.even + f2.odd) -
      (f4.even + f4.odd) - (f5.even + f5.odd) = 0

end Fuglede
