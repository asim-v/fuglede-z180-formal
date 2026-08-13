import Fuglede.Z180K18M12PairFibresLowOrder
import Fuglede.Z180K18M12PairFibresHighOrderCombinatorial

/-! # Table-free extraction of the nine same-level order-four pairs -/

namespace Fuglede

/-- The two independently proved low- and high-order adapters inhabit the
exact extraction interface from `Z180K18M12PairFibres`. -/
def z180K18M12PairFibresExtraction :
    Z180K18M12PairFibresExtractionInterface where
  low_order_fibres := z180_k18_m12_nineFibres_card_two_of_phi3_phi9
  high_order_geometry := z180_k18_m12_pairGeometry_of_high_order

/-- Unconditional pair-fibre extraction from the five cyclotomic factors. -/
theorem z180_k18_m12_pairFibres_of_cyclotomic_profile
    {A : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hinj : Set.InjOn z180K18Projection36 (A : Set (ZMod 180)))
    (h3 : Polynomial.cyclotomic 3 Int ∣ maskPolynomial 180 A)
    (h9 : Polynomial.cyclotomic 9 Int ∣ maskPolynomial 180 A)
    (h10 : Polynomial.cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : Polynomial.cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : Polynomial.cyclotomic 90 Int ∣ maskPolynomial 180 A) :
    Nonempty (Z180K18M12PairFibres A) :=
  z180_k18_m12_pairFibres_of_cyclotomic_profile_of_interface
    z180K18M12PairFibresExtraction hcard hinj h3 h9 h10 h30 h90

#print axioms z180_k18_m12_pairFibres_of_cyclotomic_profile

end Fuglede
