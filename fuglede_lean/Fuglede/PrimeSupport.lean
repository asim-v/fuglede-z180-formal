import Fuglede.InnerDistribution
import Fuglede.SupportOrder
import Fuglede.PrimeCyclotomic
import Fuglede.SpectralFourier

/-!
# Singleton-support consequences of spectrality at modulus `2310`

For a spectral pair `(A, L)`, a difference supported on one CRT coordinate
forces the corresponding prime to divide the common cardinality.  Taking the
contrapositive says that, whenever that prime does not divide the cardinality,
the singleton entry of the inner distribution vanishes on both sides of the
spectral pair.
-/

namespace Fuglede

/-- A singleton difference support is necessarily off the diagonal. -/
theorem ne_of_differenceSupport_eq_singleton
    {x y : ZMod 2310} {i : Fin 5}
    (hsupport : differenceSupport x y = {i}) : x ≠ y := by
  intro hxy
  have hi : i ∈ differenceSupport x y := by
    rw [hsupport]
    simp
  have hempty : differenceSupport x y = ∅ :=
    (differenceSupport_eq_empty_iff x y).2 hxy
  rw [hempty] at hi
  simp at hi

/-- A singleton-supported difference inside `A` is, by spectral duality, a
cyclotomic zero for the mask of `L`. -/
theorem cyclotomicZero_L_of_spectral_A_singleton_difference
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    {i : Fin 5} {x y : ZMod 2310} (hx : x ∈ A) (hy : y ∈ A)
    (hsupport : differenceSupport x y = {i}) :
    CyclotomicZero 2310 L (x - y) := by
  have hdual : CyclotomicSpectrum 2310 L A :=
    cyclotomicSpectrum_dual hSpec
  exact hdual.2.2 x hx y hy (ne_of_differenceSupport_eq_singleton hsupport)

/-- A singleton-supported difference inside `L` is directly a cyclotomic
zero for the mask of `A`. -/
theorem cyclotomicZero_A_of_spectral_L_singleton_difference
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    {i : Fin 5} {x y : ZMod 2310} (hx : x ∈ L) (hy : y ∈ L)
    (hsupport : differenceSupport x y = {i}) :
    CyclotomicZero 2310 A (x - y) :=
  hSpec.2.2 x hx y hy (ne_of_differenceSupport_eq_singleton hsupport)

/-- A difference in `A` supported on a single CRT prime forces that prime to
divide the common cardinality of the spectral pair.  The zero on `L` comes
from exact spectral duality. -/
theorem prime_dvd_card_of_spectral_A_singleton_difference
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) {x y : ZMod 2310} (hx : x ∈ A) (hy : y ∈ A)
    (hsupport : differenceSupport x y = {i}) :
    crt2310Modulus i ∣ A.card := by
  have hzero : CyclotomicZero 2310 L (x - y) :=
    cyclotomicZero_L_of_spectral_A_singleton_difference
      hSpec hx hy hsupport
  have horder : frequencyOrder 2310 (x - y) = crt2310Modulus i := by
    rw [frequencyOrder_sub_eq_supportModulus, hsupport]
    simp [supportModulus]
  have hdiv : crt2310Modulus i ∣ L.card :=
    prime_dvd_card_of_cyclotomicZero
      (crt2310Modulus_prime i) L (x - y) horder hzero
  rwa [← hSpec.2.1] at hdiv

/-- A difference in `L` supported on a single CRT prime directly supplies a
zero of the mask of `A`, hence prime divisibility of `A.card`. -/
theorem prime_dvd_card_of_spectral_L_singleton_difference
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) {x y : ZMod 2310} (hx : x ∈ L) (hy : y ∈ L)
    (hsupport : differenceSupport x y = {i}) :
    crt2310Modulus i ∣ A.card := by
  have hzero : CyclotomicZero 2310 A (x - y) :=
    cyclotomicZero_A_of_spectral_L_singleton_difference
      hSpec hx hy hsupport
  have horder : frequencyOrder 2310 (x - y) = crt2310Modulus i := by
    rw [frequencyOrder_sub_eq_supportModulus, hsupport]
    simp [supportModulus]
  exact prime_dvd_card_of_cyclotomicZero
    (crt2310Modulus_prime i) A (x - y) horder hzero

/-- If the `i`-th CRT prime does not divide the spectral cardinality, no
ordered pair of elements of `A` can have exact support `{i}`. -/
theorem innerDistribution_A_singleton_eq_zero_of_not_dvd
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card) :
    innerDistribution A {i} = 0 := by
  by_contra hne
  have hpos : 0 < innerDistribution A {i} := Nat.pos_of_ne_zero hne
  rw [innerDistribution] at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rcases p with ⟨x, y⟩
  rcases Finset.mem_filter.mp hp with ⟨hxy, hsupport⟩
  rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
  exact hnot
    (prime_dvd_card_of_spectral_A_singleton_difference
      hSpec i hx hy hsupport)

/-- The same forbidden-singleton conclusion for the spectrum `L`. -/
theorem innerDistribution_L_singleton_eq_zero_of_not_dvd
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card) :
    innerDistribution L {i} = 0 := by
  by_contra hne
  have hpos : 0 < innerDistribution L {i} := Nat.pos_of_ne_zero hne
  rw [innerDistribution] at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rcases p with ⟨x, y⟩
  rcases Finset.mem_filter.mp hp with ⟨hxy, hsupport⟩
  rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
  exact hnot
    (prime_dvd_card_of_spectral_L_singleton_difference
      hSpec i hx hy hsupport)

end Fuglede
