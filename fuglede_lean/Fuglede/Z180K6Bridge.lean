import Fuglede.CRT180RamanujanClosure
import Fuglede.ProjectionTiling
import Fuglede.Z180K6M6Graph
import Fuglede.Z180Projection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Kernel-checked bridge for the cardinality-six branch in `ZMod 180`

This module isolates the precise remaining structural input in the existing
`k = 6` argument.  Everything after the five-level descent and normalized
zero-profile classification is proved here:

* projection to `ZMod 36` is injective on both members of a spectral pair;
* the Ramanujan transform is unconditionally available (and its order-five
  row is strictly positive) on both members;
* four distinct base points in one residue class modulo a defect order `m`,
  together with `6 ∣ m ∣ 36`, force `m = 6`;
* a zero-order envelope contained in `{4, 30}` is incompatible with any
  spectrum having at least three points;
* consequently, the single structural statement that every non-tiler has
  that envelope closes spectral-to-tile at cardinality six.

No finite computation or external solver is trusted by this module.
-/

namespace Fuglede

open scoped BigOperators

/-! ## Automatic projection and Ramanujan inputs -/

/-- At cardinality six, reduction modulo `36` is injective on the set. -/
theorem z180_k6_projection36_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) := by
  apply z180_projection36_injOn_of_spectral_not_five_dvd hSpec
  norm_num [hcard]

/-- At cardinality six, reduction modulo `36` is also injective on the
spectrum. -/
theorem z180_k6_projection36_spectrum_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (L : Set (ZMod 180)) := by
  apply z180_projection36_spectrum_injOn_of_spectral_not_five_dvd hSpec
  norm_num [hcard]

/-- The unconditional Ramanujan identity makes the order-five transform row
strictly positive on both sides of a cardinality-six spectral pair.  This
records the exact-order information available before the structural descent. -/
theorem z180_k6_exactOrderTransform_five_pos_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    0 < z180ExactOrderTransform A 5 ∧
      0 < z180ExactOrderTransform L 5 := by
  have hcardL : L.card = 6 := by
    calc
      L.card = A.card := hSpec.2.1.symm
      _ = 6 := hcard
  constructor
  · exact z180ExactOrderTransform_pos_five (z180RamanujanIdentity A)
      (by norm_num [hcard])
  · exact z180ExactOrderTransform_pos_five (z180RamanujanIdentity L)
      (by norm_num [hcardL])

/-! ## The finite-capacity reduction of the defect order -/

/-- A constant fibre of reduction `ZMod 36 → ZMod m` has cardinality
`36 / m`.  The multiplicative form below avoids division: if it contains a
finite set `S`, then `m * |S| ≤ 36`.

The hypotheses `0 < m` and `m ∣ 36` are exactly those needed to form the
surjective reduction map. -/
theorem z180_k6_constant_cast_fibre_capacity
    {m : ℕ} (hmpos : 0 < m) (hm36 : m ∣ 36)
    (S : Finset (ZMod 36)) (c : ZMod m)
    (hconstant : ∀ x ∈ S, (ZMod.cast x : ZMod m) = c) :
    m * S.card ≤ 36 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  classical
  let φ : ZMod 36 →+ ZMod m :=
    (ZMod.castHom hm36 (ZMod m)).toAddMonoidHom
  let fibre : ZMod m → Finset (ZMod 36) := fun y ↦
    Finset.univ.filter fun x ↦ φ x = y
  have hsurj : Function.Surjective φ := by
    simpa [φ] using ZMod.castHom_surjective hm36
  have hfibre_eq (y : ZMod m) : (fibre y).card = (fibre c).card := by
    simpa [fibre] using
      (AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj y) (hsurj c))
  have hpartition :
      (Finset.univ : Finset (ZMod 36)).card =
        ∑ y : ZMod m, (fibre y).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod 36)))
      (t := (Finset.univ : Finset (ZMod m)))
      (f := fun x ↦ φ x) (by simp)
    simpa [fibre] using h
  have htotal : 36 = m * (fibre c).card := by
    calc
      36 = ∑ y : ZMod m, (fibre y).card := by
        simpa [ZMod.card] using hpartition
      _ = ∑ _y : ZMod m, (fibre c).card := by
        apply Finset.sum_congr rfl
        intro y _hy
        exact hfibre_eq y
      _ = m * (fibre c).card := by simp [ZMod.card]
  have hsubset : S ⊆ fibre c := by
    intro x hx
    simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [φ, ZMod.castHom_apply] using hconstant x hx
  have hcard_le : S.card ≤ (fibre c).card := Finset.card_le_card hsubset
  calc
    m * S.card ≤ m * (fibre c).card := Nat.mul_le_mul_left m hcard_le
    _ = 36 := htotal.symm

/-- The exact arithmetic end of the FKMS descent: four distinct singleton
base points in one residue class modulo `m`, together with `6 ∣ m ∣ 36`,
force the only possible defect order `m = 6`. -/
theorem z180_k6_defect_order_eq_six
    {m : ℕ} (hmpos : 0 < m) (hm36 : m ∣ 36) (h6m : 6 ∣ m)
    (S : Finset (ZMod 36)) (hcardS : S.card = 4)
    (c : ZMod m)
    (hconstant : ∀ x ∈ S, (ZMod.cast x : ZMod m) = c) :
    m = 6 := by
  have hcapacity := z180_k6_constant_cast_fibre_capacity
    hmpos hm36 S c hconstant
  rw [hcardS] at hcapacity
  obtain ⟨q, hq⟩ := h6m
  omega

/-- Set-level version used by the descent argument.  Four distinct points of
`A` remain distinct after projection modulo `36`; if their projected base
coordinates lie in one class modulo `m`, the capacity theorem forces `m=6`.

This is the formal bridge from the already-proved projection injectivity to
the arithmetic defect-order reduction. -/
theorem z180_k6_defect_order_eq_six_of_four_set_points
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    {m : ℕ} (hmpos : 0 < m) (hm36 : m ∣ 36) (h6m : 6 ∣ m)
    (T : Finset (ZMod 180)) (hTA : T ⊆ A) (hcardT : T.card = 4)
    (c : ZMod m)
    (hconstant : ∀ x ∈ T,
      (ZMod.cast (ZMod.cast x : ZMod 36) : ZMod m) = c) :
    m = 6 := by
  classical
  let base : ZMod 180 → ZMod 36 := fun x ↦ ZMod.cast x
  let S : Finset (ZMod 36) := T.image base
  have hinjA : Set.InjOn base (A : Set (ZMod 180)) := by
    simpa [base] using z180_k6_projection36_injOn_of_spectral hSpec hcard
  have hinjT : Set.InjOn base (T : Set (ZMod 180)) := by
    intro x hx y hy hxy
    exact hinjA (hTA hx) (hTA hy) hxy
  have hcardS : S.card = 4 := by
    calc
      S.card = T.card := by
        exact Finset.card_image_of_injOn hinjT
      _ = 4 := hcardT
  apply z180_k6_defect_order_eq_six hmpos hm36 h6m S hcardS c
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  simpa [base] using hconstant x hx

/-! ## The terminal `{4,30}` envelope and tiling endpoint -/

/-- The exact zero-order envelope left by the normalized `m = 6` branch. -/
def Z180K6ZeroEnvelope (A : Finset (ZMod 180)) : Prop :=
  ∀ d : ZMod 180, d ≠ 0 → CyclotomicZero 180 A d →
    Z180K6M6AllowedDifference d

/-- The terminal compatibility graph has clique number at most two. -/
theorem z180_k6_card_le_two_of_pairwise_allowed
    (L : Finset (ZMod 180))
    (hpair : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      Z180K6M6AllowedDifference (x - y)) :
    L.card ≤ 2 := by
  classical
  by_contra hle
  have hlt : 2 < L.card := Nat.lt_of_not_ge hle
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hlt
  exact z180_k6_m6_graph_triangle_free x y z
    (hpair x hx y hy hxy)
    (hpair x hx z hz hxz)
    (hpair y hy z hz hyz)

/-- A set with the `{4,30}` zero envelope cannot have a spectrum of more
than two points. -/
theorem z180_k6_spectrum_card_le_two_of_zeroEnvelope
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (henvelope : Z180K6ZeroEnvelope A) :
    L.card ≤ 2 := by
  apply z180_k6_card_le_two_of_pairwise_allowed L
  intro x hx y hy hxy
  exact henvelope (x - y) (sub_ne_zero.mpr hxy)
    (hSpec.2.2 x hx y hy hxy)

/-- In particular, the terminal envelope is impossible at cardinality six. -/
theorem z180_k6_zeroEnvelope_impossible_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (henvelope : Z180K6ZeroEnvelope A) : False := by
  have hcardL : L.card = 6 := hSpec.2.1 ▸ hcard
  have hle := z180_k6_spectrum_card_le_two_of_zeroEnvelope hSpec henvelope
  omega

/-- The one remaining mathematical bridge in the existing size-six proof:
every putative non-tiler is reduced by descent and zero classification to the
terminal `{4,30}` envelope. -/
def Z180K6NonTilerReduction (A : Finset (ZMod 180)) : Prop :=
  (¬ ∃ B : Finset (ZMod 180), Tiles A B) → Z180K6ZeroEnvelope A

/-- Conditional closure of spectral-to-tile at cardinality six.  Apart from
spectrality and cardinality, the only hypothesis is the explicitly named
non-tiler reduction above. -/
theorem z180_k6_exists_tiling_of_spectral_of_nonTilerReduction
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hreduction : Z180K6NonTilerReduction A) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_contra hnot
  exact z180_k6_zeroEnvelope_impossible_of_spectral hSpec hcard
    (hreduction hnot)

#print axioms z180_k6_projection36_injOn_of_spectral
#print axioms z180_k6_exactOrderTransform_five_pos_of_spectral
#print axioms z180_k6_defect_order_eq_six
#print axioms z180_k6_defect_order_eq_six_of_four_set_points
#print axioms z180_k6_spectrum_card_le_two_of_zeroEnvelope
#print axioms z180_k6_exists_tiling_of_spectral_of_nonTilerReduction

end Fuglede
