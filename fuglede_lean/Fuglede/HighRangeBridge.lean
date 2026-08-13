import Fuglede.PrimeSupport
import Fuglede.ProjectionCollision
import Fuglede.SupportOrder
import Fuglede.CardinalityEndpoints
import Fuglede.HighCardinalitySieve

/-!
# High-cardinality structural bridge at modulus `2310`

For a spectral pair, failure of divisibility by one of the five CRT primes
forbids a difference supported on that prime alone.  Projecting onto the
other four coordinates is consequently injective.  This gives the sharp
cardinality bound by the product of those four coordinates, and equality
makes the set a complete transversal of the projection kernel.
-/

namespace Fuglede

/-- All CRT coordinates except `i`; equivalently, the projection which
forgets the `i`-th prime coordinate. -/
def coordinatesExcept (i : Fin 5) : Finset (Fin 5) :=
  Finset.univ.erase i

@[simp]
theorem mem_coordinatesExcept {i j : Fin 5} :
    j ∈ coordinatesExcept i ↔ j ≠ i := by
  simp [coordinatesExcept]

/-- The projection which forgets `i` has exactly `2310 / p_i` possible
values. -/
theorem card_CRTProjection_coordinatesExcept (i : Fin 5) :
    Fintype.card (CRTProjection (coordinatesExcept i)) =
      2310 / crt2310Modulus i := by
  rw [Fintype.card_pi]
  simp only [ZMod.card]
  rw [← Finset.prod_subtype (coordinatesExcept i) (fun _ ↦ Iff.rfl)
    crt2310Modulus]
  have hprod :
      (∏ j ∈ coordinatesExcept i, crt2310Modulus j) *
          crt2310Modulus i = 2310 := by
    rw [coordinatesExcept,
      Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin 5)))
        (f := crt2310Modulus) (Finset.mem_univ i)]
    exact crt2310Modulus_prod
  exact (Nat.div_eq_of_eq_mul_left
    (crt2310Modulus_prime i).pos hprod.symm).symm

/-- If two distinct points have the same coordinates away from `i`, their
difference support is exactly the singleton `{i}`. -/
theorem differenceSupport_eq_singleton_of_projection_coordinatesExcept_eq
    (i : Fin 5) {x y : ZMod 2310} (hxy : x ≠ y)
    (hproj : crtProjection (coordinatesExcept i) x =
      crtProjection (coordinatesExcept i) y) :
    differenceSupport x y = {i} := by
  classical
  have hdisjoint :
      Disjoint (differenceSupport x y) (coordinatesExcept i) :=
    (crtProjection_eq_iff_disjoint (coordinatesExcept i) x y).mp hproj
  have hsubset : differenceSupport x y ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    have hjexcept : j ∈ coordinatesExcept i :=
      mem_coordinatesExcept.mpr hji
    exact (Finset.disjoint_left.mp hdisjoint) hj hjexcept
  rcases Finset.subset_singleton_iff.mp hsubset with hempty | hsingleton
  · exact False.elim (hxy ((differenceSupport_eq_empty_iff x y).mp hempty))
  · exact hsingleton

/-- Nondivisibility by the forgotten prime forces injectivity of the
four-coordinate projection on the first member of a spectral pair. -/
theorem spectral_projection_coordinatesExcept_injOn
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card) :
    Set.InjOn (crtProjection (coordinatesExcept i))
      (A : Set (ZMod 2310)) := by
  intro x hx y hy hproj
  by_contra hxy
  have hsupport : differenceSupport x y = {i} :=
    differenceSupport_eq_singleton_of_projection_coordinatesExcept_eq
      i hxy hproj
  exact hnot
    (prime_dvd_card_of_spectral_A_singleton_difference
      hSpec i hx hy hsupport)

/-- The same injectivity statement on the spectrum member `L`. -/
theorem spectral_spectrum_projection_coordinatesExcept_injOn
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card) :
    Set.InjOn (crtProjection (coordinatesExcept i))
      (L : Set (ZMod 2310)) := by
  intro x hx y hy hproj
  by_contra hxy
  have hsupport : differenceSupport x y = {i} :=
    differenceSupport_eq_singleton_of_projection_coordinatesExcept_eq
      i hxy hproj
  exact hnot
    (prime_dvd_card_of_spectral_L_singleton_difference
      hSpec i hx hy hsupport)

/-- Sharp cardinality bound obtained by forgetting a nondividing prime
coordinate. -/
theorem spectral_card_le_quotient_of_not_prime_dvd
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card) :
    A.card ≤ 2310 / crt2310Modulus i := by
  have hinj := spectral_projection_coordinatesExcept_injOn hSpec i hnot
  have hfinite :
      Fintype.card (A : Set (ZMod 2310)) ≤
        Fintype.card (CRTProjection (coordinatesExcept i)) := by
    apply Fintype.card_le_of_injective
      (fun a : (A : Set (ZMod 2310)) ↦
        crtProjection (coordinatesExcept i) a.1)
    intro a b hab
    apply Subtype.ext
    exact hinj a.2 b.2 hab
  simpa [card_CRTProjection_coordinatesExcept i] using hfinite

/-- Equality in the projection bound makes `A` a complete transversal, so
it tiles by the kernel of the forgotten-coordinate projection. -/
theorem spectral_tiles_projection_kernel_of_not_prime_dvd_of_card_eq
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hnot : ¬ crt2310Modulus i ∣ A.card)
    (hcard : A.card = 2310 / crt2310Modulus i) :
    Tiles A (kernelFinset (crtProjection (coordinatesExcept i))) := by
  apply transversal_tiles_kernel (crtProjection (coordinatesExcept i)) A
  · exact (kernel_difference_free_iff_injOn
      (crtProjection (coordinatesExcept i)) A).2
      (spectral_projection_coordinatesExcept_injOn hSpec i hnot)
  · rw [card_CRTProjection_coordinatesExcept]
    exact hcard

/-- Contrapositive form of the projection bound: exceeding the product of
the other four CRT coordinates forces divisibility by the omitted prime. -/
theorem prime_dvd_spectral_card_of_quotient_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (i : Fin 5) (hlarge : 2310 / crt2310Modulus i < A.card) :
    crt2310Modulus i ∣ A.card := by
  by_contra hnot
  have hbound :=
    spectral_card_le_quotient_of_not_prime_dvd hSpec i hnot
  omega

/-- Above `210 = 2310 / 11`, spectral cardinality is divisible by `11`. -/
theorem eleven_dvd_spectral_card_of_210_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hlarge : 210 < A.card) : 11 ∣ A.card := by
  simpa [crt2310Modulus] using
    prime_dvd_spectral_card_of_quotient_lt hSpec (4 : Fin 5) hlarge

/-- Above `330 = 2310 / 7`, spectral cardinality is divisible by `7`. -/
theorem seven_dvd_spectral_card_of_330_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hlarge : 330 < A.card) : 7 ∣ A.card := by
  simpa [crt2310Modulus] using
    prime_dvd_spectral_card_of_quotient_lt hSpec (3 : Fin 5) hlarge

/-- Above `462 = 2310 / 5`, spectral cardinality is divisible by `5`. -/
theorem five_dvd_spectral_card_of_462_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hlarge : 462 < A.card) : 5 ∣ A.card := by
  simpa [crt2310Modulus] using
    prime_dvd_spectral_card_of_quotient_lt hSpec (2 : Fin 5) hlarge

/-- Above `770 = 2310 / 3`, spectral cardinality is divisible by `3`. -/
theorem three_dvd_spectral_card_of_770_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hlarge : 770 < A.card) : 3 ∣ A.card := by
  simpa [crt2310Modulus] using
    prime_dvd_spectral_card_of_quotient_lt hSpec (1 : Fin 5) hlarge

/-- Above `1155 = 2310 / 2`, spectral cardinality is divisible by `2`. -/
theorem two_dvd_spectral_card_of_1155_lt
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hlarge : 1155 < A.card) : 2 ∣ A.card := by
  simpa [crt2310Modulus] using
    prime_dvd_spectral_card_of_quotient_lt hSpec (0 : Fin 5) hlarge

/-- The five threshold implications, collected in the exact order used by
the high-cardinality sieve. -/
theorem spectral_card_prime_thresholds
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L) :
    (210 < A.card → 11 ∣ A.card) ∧
    (330 < A.card → 7 ∣ A.card) ∧
    (462 < A.card → 5 ∣ A.card) ∧
    (770 < A.card → 3 ∣ A.card) ∧
    (1155 < A.card → 2 ∣ A.card) := by
  exact ⟨eleven_dvd_spectral_card_of_210_lt hSpec,
    seven_dvd_spectral_card_of_330_lt hSpec,
    five_dvd_spectral_card_of_462_lt hSpec,
    three_dvd_spectral_card_of_770_lt hSpec,
    two_dvd_spectral_card_of_1155_lt hSpec⟩

/-- A proper cyclotomic spectral subset of `ZMod 2310` has at most `1155`
elements. -/
theorem proper_cyclotomicSpectrum_card_le_1155
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hproper : A ≠ Finset.univ) : A.card ≤ 1155 := by
  have hFourier : FourierSpectrum A L :=
    (cyclotomicSpectrum_iff_fourierSpectrum A L).mp hSpec
  have hhalf := proper_fourierSpectrum_card_le_half hFourier hproper
  have hhalf2310 : 2 * A.card ≤ 2310 := by
    simpa using hhalf
  omega

/-- End-to-end high-range reduction: if a proper spectral subset has more
than `210` elements, its cardinality is one of the fifteen values surviving
the arithmetic sieve. -/
theorem proper_spectral_high_cardinality_candidates
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hproper : A ≠ Finset.univ) (hlarge : 210 < A.card) :
    A.card = 220 ∨ A.card = 231 ∨ A.card = 242 ∨
    A.card = 253 ∨ A.card = 264 ∨ A.card = 275 ∨
    A.card = 286 ∨ A.card = 297 ∨ A.card = 308 ∨
    A.card = 319 ∨ A.card = 330 ∨ A.card = 385 ∨
    A.card = 462 ∨ A.card = 770 ∨ A.card = 1155 := by
  rcases spectral_card_prime_thresholds hSpec with
    ⟨h11, h7, h5, h3, _h2⟩
  exact high_cardinality_arithmetic_sieve A.card hlarge
    (proper_cyclotomicSpectrum_card_le_1155 hSpec hproper)
    (h11 hlarge) h7 h5 h3

/-- The four quotient-size endpoints in the high-cardinality sieve already
tile by a projection kernel.  Consequently, a proper spectral set above
`210` either tiles or has one of the eleven cardinalities which remain for
the multiaxis certificates. -/
theorem proper_spectral_high_cardinality_tiles_or_core_candidates
    {A L : Finset (ZMod 2310)} (hSpec : CyclotomicSpectrum 2310 A L)
    (hproper : A ≠ Finset.univ) (hlarge : 210 < A.card) :
    (∃ B : Finset (ZMod 2310), Tiles A B) ∨
    A.card = 220 ∨ A.card = 231 ∨ A.card = 242 ∨
    A.card = 253 ∨ A.card = 264 ∨ A.card = 275 ∨
    A.card = 286 ∨ A.card = 297 ∨ A.card = 308 ∨
    A.card = 319 ∨ A.card = 385 := by
  rcases proper_spectral_high_cardinality_candidates hSpec hproper hlarge with
    h220 | h231 | h242 | h253 | h264 | h275 | h286 | h297 |
      h308 | h319 | h330 | h385 | h462 | h770 | h1155
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · right
    aesop
  · left
    refine ⟨kernelFinset
      (crtProjection (coordinatesExcept (3 : Fin 5))), ?_⟩
    apply spectral_tiles_projection_kernel_of_not_prime_dvd_of_card_eq
      hSpec (3 : Fin 5)
    · change ¬ 7 ∣ A.card
      rw [h330]
      norm_num
    · change A.card = 330
      exact h330
  · right
    aesop
  · left
    refine ⟨kernelFinset
      (crtProjection (coordinatesExcept (2 : Fin 5))), ?_⟩
    apply spectral_tiles_projection_kernel_of_not_prime_dvd_of_card_eq
      hSpec (2 : Fin 5)
    · change ¬ 5 ∣ A.card
      rw [h462]
      norm_num
    · change A.card = 462
      exact h462
  · left
    refine ⟨kernelFinset
      (crtProjection (coordinatesExcept (1 : Fin 5))), ?_⟩
    apply spectral_tiles_projection_kernel_of_not_prime_dvd_of_card_eq
      hSpec (1 : Fin 5)
    · change ¬ 3 ∣ A.card
      rw [h770]
      norm_num
    · change A.card = 770
      exact h770
  · left
    refine ⟨kernelFinset
      (crtProjection (coordinatesExcept (0 : Fin 5))), ?_⟩
    apply spectral_tiles_projection_kernel_of_not_prime_dvd_of_card_eq
      hSpec (0 : Fin 5)
    · change ¬ 2 ∣ A.card
      rw [h1155]
      norm_num
    · change A.card = 1155
      exact h1155

end Fuglede
