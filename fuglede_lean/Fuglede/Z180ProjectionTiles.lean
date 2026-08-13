import Fuglede.Z180Projection
import Fuglede.Z180ExactOrderTransform
import Fuglede.ProjectionTiling
import Mathlib.Tactic

/-!
# Projection tilings at cardinalities 20, 36, and 45 in `ZMod 180`

At these three cardinalities, two distinct points in one projection fibre
have prime-power difference order for a prime not dividing the cardinality.
Spectral duality and evaluation of a cyclotomic divisor at one therefore make
the projection injective.  Since the target has exactly the cardinality of
the set, the set is a complete transversal and tiles by the projection
kernel.
-/

namespace Fuglede

/-- A nonzero element in the kernel of `ZMod 180 -> ZMod 20` has order three
or nine. -/
theorem z180_frequencyOrder_three_or_nine_of_cast20_eq :
    ∀ x y : ZMod 180,
      x ≠ y ->
      (ZMod.cast x : ZMod 20) = ZMod.cast y ->
      frequencyOrder 180 (x - y) = 3 ∨ frequencyOrder 180 (x - y) = 9 := by
  intro x y hxy hcast
  have hcastZero : (ZMod.cast (x - y) : ZMod 20) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 20 ∣ 180), hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 20) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 20 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 20).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 9 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

/-- A nonzero element in the kernel of `ZMod 180 -> ZMod 45` has order two
or four. -/
theorem z180_frequencyOrder_two_or_four_of_cast45_eq :
    ∀ x y : ZMod 180,
      x ≠ y ->
      (ZMod.cast x : ZMod 45) = ZMod.cast y ->
      frequencyOrder 180 (x - y) = 2 ∨ frequencyOrder 180 (x - y) = 4 := by
  intro x y hxy hcast
  have hcastZero : (ZMod.cast (x - y) : ZMod 45) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 45 ∣ 180), hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 45) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 45 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 45).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 4 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

private theorem three_dvd_card_of_cyclotomicZero_order_three_or_nine
    {X : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 3 ∨ frequencyOrder 180 d = 9)
    (hzero : CyclotomicZero 180 X d) :
    3 ∣ X.card := by
  rcases horder with hthree | hnine
  · exact prime_dvd_card_of_cyclotomicZero (by norm_num) X d hthree hzero
  · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
      (p := 3) (N := 180) (by norm_num) 1 X
    simpa [CyclotomicZero, hnine] using hzero

private theorem two_dvd_card_of_cyclotomicZero_order_two_or_four
    {X : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 2 ∨ frequencyOrder 180 d = 4)
    (hzero : CyclotomicZero 180 X d) :
    2 ∣ X.card := by
  rcases horder with htwo | hfour
  · exact prime_dvd_card_of_cyclotomicZero (by norm_num) X d htwo hzero
  · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
      (p := 2) (N := 180) (by norm_num) 1 X
    simpa [CyclotomicZero, hfour] using hzero

theorem z180_projection20_injOn_of_spectral_card_twenty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 20) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 20))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hdual : CyclotomicSpectrum 180 L A := cyclotomicSpectrum_dual hSpec
  have hzero : CyclotomicZero 180 L (x - y) :=
    hdual.2.2 x hx y hy hxy
  have hdivL : 3 ∣ L.card :=
    three_dvd_card_of_cyclotomicZero_order_three_or_nine
      (z180_frequencyOrder_three_or_nine_of_cast20_eq x y hxy hcast) hzero
  have hdivA : 3 ∣ A.card := by simpa [hSpec.2.1] using hdivL
  omega

theorem z180_projection45_injOn_of_spectral_card_forty_five
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 45) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 45))
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hdual : CyclotomicSpectrum 180 L A := cyclotomicSpectrum_dual hSpec
  have hzero : CyclotomicZero 180 L (x - y) :=
    hdual.2.2 x hx y hy hxy
  have hdivL : 2 ∣ L.card :=
    two_dvd_card_of_cyclotomicZero_order_two_or_four
      (z180_frequencyOrder_two_or_four_of_cast45_eq x y hxy hcast) hzero
  have hdivA : 2 ∣ A.card := by simpa [hSpec.2.1] using hdivL
  omega

theorem z180_exists_tiling_of_spectral_card_twenty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 20) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  let phi : ZMod 180 →+ ZMod 20 :=
    (ZMod.castHom (by norm_num : 20 ∣ 180) (ZMod 20)).toAddMonoidHom
  refine ⟨kernelFinset phi, ?_⟩
  apply transversal_tiles_kernel phi A
  · apply (kernel_difference_free_iff_injOn phi A).2
    have hinj := z180_projection20_injOn_of_spectral_card_twenty hSpec hcard
    intro x hx y hy hmap
    apply hinj hx hy
    simpa [phi, ZMod.castHom_apply] using hmap
  · simpa [ZMod.card] using hcard

theorem z180_exists_tiling_of_spectral_card_thirty_six
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 36) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  let phi : ZMod 180 →+ ZMod 36 :=
    (ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod 36)).toAddMonoidHom
  refine ⟨kernelFinset phi, ?_⟩
  apply transversal_tiles_kernel phi A
  · apply (kernel_difference_free_iff_injOn phi A).2
    have hinj := z180_projection36_injOn_of_spectral_not_five_dvd
      hSpec (by omega)
    intro x hx y hy hmap
    apply hinj hx hy
    simpa [phi, ZMod.castHom_apply] using hmap
  · simpa [ZMod.card] using hcard

theorem z180_exists_tiling_of_spectral_card_forty_five
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 45) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  let phi : ZMod 180 →+ ZMod 45 :=
    (ZMod.castHom (by norm_num : 45 ∣ 180) (ZMod 45)).toAddMonoidHom
  refine ⟨kernelFinset phi, ?_⟩
  apply transversal_tiles_kernel phi A
  · apply (kernel_difference_free_iff_injOn phi A).2
    have hinj := z180_projection45_injOn_of_spectral_card_forty_five hSpec hcard
    intro x hx y hy hmap
    apply hinj hx hy
    simpa [phi, ZMod.castHom_apply] using hmap
  · simpa [ZMod.card] using hcard

#print axioms z180_exists_tiling_of_spectral_card_twenty
#print axioms z180_exists_tiling_of_spectral_card_thirty_six
#print axioms z180_exists_tiling_of_spectral_card_forty_five

end Fuglede
