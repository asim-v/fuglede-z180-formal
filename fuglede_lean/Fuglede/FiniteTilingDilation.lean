import Fuglede.FiniteTiling
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Dilation of an odd tile by two

This file proves the finite cyclic form of the prime-dilation argument that
we need below.  If `A + B` is an exact tiling and `A` has odd cardinality,
then doubling every element of `A` still gives an exact tiling with the same
complement.

The proof works over the group algebra with coefficients in `ZMod 2`.
Frobenius turns the square of the mask of `A` into the (possibly
multiplicity-weighted) mask of `2A`.  Its product with the mask of `B` is the
uniform mask because `A + B` tiles and `|A|` is odd.  Hence every group
element has a doubled representation.  A cardinality squeeze then upgrades
surjectivity to exact tiling and, in particular, proves that doubling did not
identify two points of `A`.
-/

namespace Fuglede

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Prime dilation -/

/-- The indicator mask of a finite set over the prime field `ZMod p`. -/
noncomputable def primeMask (p : ℕ) (A : Finset G) :
    AddMonoidAlgebra (ZMod p) G :=
  ∑ a ∈ A, AddMonoidAlgebra.single a 1

/-- The uniform group-algebra mask over `ZMod p`. -/
noncomputable def primeFullMask (p : ℕ) :
    AddMonoidAlgebra (ZMod p) G :=
  ∑ g : G, AddMonoidAlgebra.single g 1

private theorem primeFinsetSum_apply {p : ℕ} {X : Type*} (s : Finset X)
    (f : X → AddMonoidAlgebra (ZMod p) G) (g : G) :
    (∑ x ∈ s, f x) g = ∑ x ∈ s, f x g := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert x s hx ih => simp [hx, ih]

private theorem primeMask_mul_of_tiles (p : ℕ) {A B : Finset G}
    (hTiles : Tiles A B) :
    primeMask p A * primeMask p B = primeFullMask p := by
  let e : ↑(A ×ˢ B) ≃ G := Equiv.ofBijective (sumMap A B) hTiles
  rw [primeMask, primeMask, primeFullMask, Finset.sum_mul_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  calc
    (∑ a ∈ A, ∑ b ∈ B,
        AddMonoidAlgebra.single (a + b) (1 : ZMod p)) =
        ∑ q ∈ A ×ˢ B,
          AddMonoidAlgebra.single (q.1 + q.2) (1 : ZMod p) :=
      (Finset.sum_product A B (fun q ↦
        AddMonoidAlgebra.single (q.1 + q.2) (1 : ZMod p))).symm
    _ = ∑ q : ↑(A ×ˢ B),
          AddMonoidAlgebra.single (q.1.1 + q.1.2) (1 : ZMod p) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (A ×ˢ B) (fun q ↦
          AddMonoidAlgebra.single (q.1 + q.2) (1 : ZMod p))).symm
    _ = ∑ g : G, AddMonoidAlgebra.single g (1 : ZMod p) :=
      Fintype.sum_equiv e _ _ (fun q ↦ rfl)

private theorem primeMask_pow (p : ℕ) [Fact p.Prime] (A : Finset G) :
    primeMask p A ^ p =
      ∑ a ∈ A, AddMonoidAlgebra.single (p • a) (1 : ZMod p) := by
  letI : ExpChar (AddMonoidAlgebra (ZMod p) G) p :=
    expChar_of_injective_ringHom
      (f := AddMonoidAlgebra.singleZeroRingHom)
      (by
        intro x y hxy
        have h := congrArg (fun f : AddMonoidAlgebra (ZMod p) G ↦ f 0) hxy
        simpa using h)
      p
  rw [primeMask, sum_pow_char]
  simp only [AddMonoidAlgebra.single_pow, one_pow]

private theorem single_mul_primeFullMask (p : ℕ) (a : G) :
    AddMonoidAlgebra.single a (1 : ZMod p) * primeFullMask p =
      primeFullMask p := by
  rw [primeFullMask, Finset.mul_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ ↦ rfl)

private theorem primeMask_mul_full (p : ℕ) (A : Finset G) :
    primeMask p A * primeFullMask p =
      (A.card : ZMod p) • primeFullMask p := by
  rw [primeMask, Finset.sum_mul]
  simp_rw [single_mul_primeFullMask]
  rw [Finset.sum_const]
  exact (Nat.cast_smul_eq_nsmul (ZMod p) A.card (primeFullMask p)).symm

private theorem primeMask_pow_mul_full (p n : ℕ) (A : Finset G) :
    primeMask p A ^ n * primeFullMask p =
      ((A.card : ZMod p) ^ n) • primeFullMask p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, primeMask_mul_full, mul_smul_comm, ih]
      rw [smul_smul, pow_succ']

private theorem dilated_prime_mask_mul_of_tiles
    (p : ℕ) [Fact p.Prime] {A B : Finset G}
    (hTiles : Tiles A B) (hnot : ¬p ∣ A.card) :
    (∑ a ∈ A, AddMonoidAlgebra.single (p • a) (1 : ZMod p)) *
        primeMask p B = primeFullMask p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcast : (A.card : ZMod p) ≠ 0 := by
    intro hz
    exact hnot ((ZMod.natCast_eq_zero_iff A.card p).mp hz)
  rw [← primeMask_pow]
  calc
    primeMask p A ^ p * primeMask p B =
        primeMask p A ^ (p - 1) *
          (primeMask p A * primeMask p B) := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
    _ = primeMask p A ^ (p - 1) * primeFullMask p := by
      rw [primeMask_mul_of_tiles p hTiles]
    _ = ((A.card : ZMod p) ^ (p - 1)) • primeFullMask p :=
      primeMask_pow_mul_full p (p - 1) A
    _ = primeFullMask p := by
      rw [ZMod.pow_card_sub_one_eq_one hcast, one_smul]

/-- Every element has a representation `p • a + b` after prime dilation. -/
theorem exists_prime_nsmul_add_rep_of_tiles_of_not_dvd_card
    (p : ℕ) [Fact p.Prime] {A B : Finset G}
    (hTiles : Tiles A B) (hnot : ¬p ∣ A.card) (g : G) :
    ∃ a ∈ A, ∃ b ∈ B, p • a + b = g := by
  have hmask := dilated_prime_mask_mul_of_tiles p hTiles hnot
  have hsum :
      (∑ a ∈ A, ∑ b ∈ B,
        AddMonoidAlgebra.single (p • a + b) (1 : ZMod p)) =
        primeFullMask p := by
    calc
      (∑ a ∈ A, ∑ b ∈ B,
          AddMonoidAlgebra.single (p • a + b) (1 : ZMod p)) =
          (∑ a ∈ A, AddMonoidAlgebra.single (p • a) (1 : ZMod p)) *
            primeMask p B := by
        rw [primeMask, Finset.sum_mul_sum]
        simp only [AddMonoidAlgebra.single_mul_single, one_mul]
      _ = primeFullMask p := hmask
  have hcoeff := congrArg (fun f : AddMonoidAlgebra (ZMod p) G ↦ f g) hsum
  rw [primeFinsetSum_apply] at hcoeff
  simp_rw [primeFinsetSum_apply] at hcoeff
  simp only [AddMonoidAlgebra.single_apply] at hcoeff
  by_contra h
  push Not at h
  have hleft :
      (∑ a ∈ A, ∑ b ∈ B,
        if p • a + b = g then (1 : ZMod p) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    simp [h a ha b hb]
  rw [hleft] at hcoeff
  have hfullcoeff : primeFullMask p g = (1 : ZMod p) := by
    rw [primeFullMask]
    change (∑ x ∈ Finset.univ,
      AddMonoidAlgebra.single x (1 : ZMod p)) g = 1
    rw [primeFinsetSum_apply]
    simp
  rw [hfullcoeff] at hcoeff
  exact zero_ne_one hcoeff

/-- Prime dilation preserves an exact tiling whenever the prime does not
divide the cardinality of the dilated factor. -/
theorem tiles_image_prime_nsmul_left_of_not_dvd_card
    (p : ℕ) [Fact p.Prime] {A B : Finset G}
    (hTiles : Tiles A B) (hnot : ¬p ∣ A.card) :
    Tiles (A.image (fun a ↦ p • a)) B := by
  let Ap : Finset G := A.image (fun a ↦ p • a)
  have hsurj : Function.Surjective (sumMap Ap B) := by
    intro g
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_prime_nsmul_add_rep_of_tiles_of_not_dvd_card p hTiles hnot g
    have hpa : p • a ∈ Ap := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    refine ⟨⟨(p • a, b), Finset.mem_product.mpr ⟨hpa, hb⟩⟩, ?_⟩
    simpa [sumMap] using hab
  apply (Fintype.bijective_iff_surjective_and_card (sumMap Ap B)).mpr
  refine ⟨hsurj, ?_⟩
  apply Nat.le_antisymm
  · calc
      Fintype.card ↑(Ap ×ˢ B) = (Ap ×ˢ B).card := Fintype.card_coe _
      _ = Ap.card * B.card := Finset.card_product Ap B
      _ ≤ A.card * B.card := Nat.mul_le_mul_right B.card Finset.card_image_le
      _ = Fintype.card G := card_mul_eq_card_of_tiles hTiles
  · exact Fintype.card_le_of_surjective (sumMap Ap B) hsurj

/-- The indicator mask of a finite set, in the group algebra over `ZMod 2`. -/
noncomputable def parityMask (A : Finset G) : AddMonoidAlgebra (ZMod 2) G :=
  ∑ a ∈ A, AddMonoidAlgebra.single a 1

/-- The mask which has coefficient one at every group element. -/
noncomputable def parityFullMask : AddMonoidAlgebra (ZMod 2) G :=
  ∑ g : G, AddMonoidAlgebra.single g 1

private theorem parityFinsetSum_apply {X : Type*} (s : Finset X)
    (f : X → AddMonoidAlgebra (ZMod 2) G) (g : G) :
    (∑ x ∈ s, f x) g = ∑ x ∈ s, f x g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (0 : ZMod 2) = 0
      rfl
  | @insert x s hx ih => simp [hx, ih]

private theorem parityMask_mul_of_tiles {A B : Finset G} (hTiles : Tiles A B) :
    parityMask A * parityMask B = (parityFullMask : AddMonoidAlgebra (ZMod 2) G) := by
  let e : ↑(A ×ˢ B) ≃ G := Equiv.ofBijective (sumMap A B) hTiles
  rw [parityMask, parityMask, parityFullMask, Finset.sum_mul_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  calc
    (∑ a ∈ A, ∑ b ∈ B,
        AddMonoidAlgebra.single (a + b) (1 : ZMod 2)) =
        ∑ p ∈ A ×ˢ B,
          AddMonoidAlgebra.single (p.1 + p.2) (1 : ZMod 2) :=
      (Finset.sum_product A B (fun p ↦
        AddMonoidAlgebra.single (p.1 + p.2) (1 : ZMod 2))).symm
    _ = ∑ p : ↑(A ×ˢ B),
          AddMonoidAlgebra.single (p.1.1 + p.1.2) (1 : ZMod 2) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (A ×ˢ B) (fun p ↦
          AddMonoidAlgebra.single (p.1 + p.2) (1 : ZMod 2))).symm
    _ = ∑ g : G, AddMonoidAlgebra.single g (1 : ZMod 2) :=
      Fintype.sum_equiv e _ _ (fun p ↦ rfl)

private theorem parityMask_sq (A : Finset G) :
    parityMask A ^ 2 =
      ∑ a ∈ A, AddMonoidAlgebra.single (2 • a) (1 : ZMod 2) := by
  letI : ExpChar (AddMonoidAlgebra (ZMod 2) G) 2 :=
    expChar_of_injective_ringHom
      (f := AddMonoidAlgebra.singleZeroRingHom)
      (by
        intro x y hxy
        have h := congrArg (fun f : AddMonoidAlgebra (ZMod 2) G ↦ f 0) hxy
        simpa using h)
      2
  rw [parityMask, sum_pow_char]
  simp only [pow_two, AddMonoidAlgebra.single_mul_single, one_mul, two_nsmul]

private theorem single_mul_parityFullMask (a : G) :
    AddMonoidAlgebra.single a (1 : ZMod 2) * parityFullMask =
      (parityFullMask : AddMonoidAlgebra (ZMod 2) G) := by
  rw [parityFullMask, Finset.mul_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ ↦ rfl)

private theorem parityMask_mul_full_of_odd (A : Finset G) (hOdd : Odd A.card) :
    parityMask A * parityFullMask =
      (parityFullMask : AddMonoidAlgebra (ZMod 2) G) := by
  rw [parityMask, Finset.sum_mul]
  simp_rw [single_mul_parityFullMask]
  obtain ⟨k, hk⟩ := hOdd
  rw [Finset.sum_const]
  have htwo : 2 • (parityFullMask : AddMonoidAlgebra (ZMod 2) G) = 0 := by
    rw [two_nsmul]
    ext g
    change parityFullMask g + parityFullMask g = 0
    rw [← two_mul]
    have hchar : (2 : ZMod 2) = 0 := by decide
    rw [hchar, zero_mul]
  calc
    A.card • (parityFullMask : AddMonoidAlgebra (ZMod 2) G) =
        (2 * k + 1) • parityFullMask := by rw [hk]
    _ = (2 * k) • parityFullMask + 1 • parityFullMask := by
      rw [add_nsmul]
    _ = k • (2 • parityFullMask) + parityFullMask := by
      rw [mul_nsmul, one_nsmul]
    _ = parityFullMask := by rw [htwo]; simp

private theorem doubled_mask_mul_of_tiles_of_odd {A B : Finset G}
    (hTiles : Tiles A B) (hOdd : Odd A.card) :
    (∑ a ∈ A, AddMonoidAlgebra.single (2 • a) (1 : ZMod 2)) * parityMask B =
      (parityFullMask : AddMonoidAlgebra (ZMod 2) G) := by
  rw [← parityMask_sq]
  calc
    parityMask A ^ 2 * parityMask B =
        parityMask A * (parityMask A * parityMask B) := by
      simp [pow_two, mul_assoc]
    _ = parityMask A * parityFullMask := by rw [parityMask_mul_of_tiles hTiles]
    _ = parityFullMask := parityMask_mul_full_of_odd A hOdd

/-- Every group element has a representation `2a + b` when `A + B` tiles
and `A` has odd cardinality.  At this stage `a` is retained, so no
injectivity of doubling is assumed. -/
theorem exists_double_add_rep_of_tiles_of_odd_card {A B : Finset G}
    (hTiles : Tiles A B) (hOdd : Odd A.card) (g : G) :
    ∃ a ∈ A, ∃ b ∈ B, 2 • a + b = g := by
  have hmask := doubled_mask_mul_of_tiles_of_odd hTiles hOdd
  have hsum :
      (∑ a ∈ A, ∑ b ∈ B,
        AddMonoidAlgebra.single (2 • a + b) (1 : ZMod 2)) =
        (parityFullMask : AddMonoidAlgebra (ZMod 2) G) := by
    calc
      (∑ a ∈ A, ∑ b ∈ B,
          AddMonoidAlgebra.single (2 • a + b) (1 : ZMod 2)) =
          (∑ a ∈ A, AddMonoidAlgebra.single (2 • a) (1 : ZMod 2)) *
            parityMask B := by
        rw [parityMask, Finset.sum_mul_sum]
        simp only [AddMonoidAlgebra.single_mul_single, one_mul]
      _ = parityFullMask := hmask
  have hcoeff := congrArg (fun f : AddMonoidAlgebra (ZMod 2) G ↦ f g) hsum
  rw [parityFinsetSum_apply] at hcoeff
  simp_rw [parityFinsetSum_apply] at hcoeff
  simp only [AddMonoidAlgebra.single_apply] at hcoeff
  by_contra h
  push_neg at h
  have hleft :
      (∑ x ∈ A, ∑ x_1 ∈ B,
        if 2 • x + x_1 = g then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    simp [h a ha b hb]
  rw [hleft] at hcoeff
  have hfullcoeff : parityFullMask g = (1 : ZMod 2) := by
    rw [parityFullMask]
    change (∑ x ∈ Finset.univ,
      AddMonoidAlgebra.single x (1 : ZMod 2)) g = 1
    rw [parityFinsetSum_apply]
    simp
  rw [hfullcoeff] at hcoeff
  exact zero_ne_one hcoeff

/-- Prime-dilation lemma at the prime two.  No injectivity hypothesis on the
doubling map is needed: it follows from exact tiling and the cardinality
squeeze in the proof. -/
theorem tiles_image_two_nsmul_left_of_odd_card {A B : Finset G}
    (hTiles : Tiles A B) (hOdd : Odd A.card) :
    Tiles (A.image (fun a ↦ 2 • a)) B := by
  let A2 : Finset G := A.image (fun a ↦ 2 • a)
  have hsurj : Function.Surjective (sumMap A2 B) := by
    intro g
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_double_add_rep_of_tiles_of_odd_card hTiles hOdd g
    have h2a : 2 • a ∈ A2 := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    refine ⟨⟨(2 • a, b), Finset.mem_product.mpr ⟨h2a, hb⟩⟩, ?_⟩
    simpa [sumMap] using hab
  apply (Fintype.bijective_iff_surjective_and_card (sumMap A2 B)).mpr
  refine ⟨hsurj, ?_⟩
  apply Nat.le_antisymm
  · calc
      Fintype.card ↑(A2 ×ˢ B) = (A2 ×ˢ B).card := Fintype.card_coe _
      _ = A2.card * B.card := Finset.card_product A2 B
      _ ≤ A.card * B.card := Nat.mul_le_mul_right B.card (Finset.card_image_le)
      _ = Fintype.card G := card_mul_eq_card_of_tiles hTiles
  · exact Fintype.card_le_of_surjective (sumMap A2 B) hsurj

/-- The part of a finite set lying in an additive subgroup, regarded as a
finset of elements of that subgroup. -/
noncomputable def finsetInAddSubgroup (H : AddSubgroup G) (A : Finset G) :
    Finset H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact Finset.univ.filter fun x ↦ (x.1 : G) ∈ A

@[simp]
theorem mem_finsetInAddSubgroup (H : AddSubgroup G) (A : Finset G) (x : H) :
    x ∈ finsetInAddSubgroup H A ↔ (x.1 : G) ∈ A := by
  classical
  simp [finsetInAddSubgroup]

/-- Restrict an exact tiling to a subgroup containing its first factor. -/
theorem tiles_restrict_to_addSubgroup (H : AddSubgroup G) {A B : Finset G}
    (hA : ∀ a ∈ A, a ∈ H) (hTiles : Tiles A B) :
    Tiles (finsetInAddSubgroup H A) (finsetInAddSubgroup H B) := by
  classical
  constructor
  · intro x y hxy
    have hax : (x.1.1.1 : G) ∈ A :=
      (mem_finsetInAddSubgroup H A x.1.1).mp
        (Finset.mem_product.mp x.2).1
    have hbx : (x.1.2.1 : G) ∈ B :=
      (mem_finsetInAddSubgroup H B x.1.2).mp
        (Finset.mem_product.mp x.2).2
    have hay : (y.1.1.1 : G) ∈ A :=
      (mem_finsetInAddSubgroup H A y.1.1).mp
        (Finset.mem_product.mp y.2).1
    have hby : (y.1.2.1 : G) ∈ B :=
      (mem_finsetInAddSubgroup H B y.1.2).mp
        (Finset.mem_product.mp y.2).2
    let px : ↑(A ×ˢ B) := ⟨((x.1.1.1 : G), (x.1.2.1 : G)),
      Finset.mem_product.mpr ⟨hax, hbx⟩⟩
    let py : ↑(A ×ˢ B) := ⟨((y.1.1.1 : G), (y.1.2.1 : G)),
      Finset.mem_product.mpr ⟨hay, hby⟩⟩
    have hp : px = py := hTiles.1 (by
      have hxyG := congrArg (fun z : H ↦ (z.1 : G)) hxy
      simpa [px, py, sumMap] using hxyG)
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : ↑(A ×ˢ B) ↦ p.1.1) hp
    · apply Subtype.ext
      exact congrArg (fun p : ↑(A ×ˢ B) ↦ p.1.2) hp
  · intro g
    obtain ⟨p, hp⟩ := hTiles.2 (g.1 : G)
    have ha := (Finset.mem_product.mp p.2).1
    have hb := (Finset.mem_product.mp p.2).2
    have haH : p.1.1 ∈ H := hA p.1.1 ha
    have hbH : p.1.2 ∈ H := by
      have heq : p.1.2 = (g.1 : G) - p.1.1 := by
        have hp' := hp
        simp only [sumMap] at hp'
        rw [← hp']
        simp
      rw [heq]
      exact H.sub_mem g.2 haH
    let aH : H := ⟨p.1.1, haH⟩
    let bH : H := ⟨p.1.2, hbH⟩
    refine ⟨⟨(aH, bH), Finset.mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact (mem_finsetInAddSubgroup H A aH).mpr ha
    · exact (mem_finsetInAddSubgroup H B bH).mpr hb
    · apply Subtype.ext
      simpa [aH, bH, sumMap] using hp

omit [Fintype G] [DecidableEq G] in
/-- Exact tilings are transported by additive equivalences. -/
theorem tiles_image_addEquiv {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (e : G ≃+ H) {A B : Finset G} (hTiles : Tiles A B) :
    Tiles (A.image e) (B.image e) := by
  constructor
  · intro x y hxy
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp (Finset.mem_product.mp x.2).1
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp (Finset.mem_product.mp x.2).2
    obtain ⟨a', ha', hay⟩ := Finset.mem_image.mp (Finset.mem_product.mp y.2).1
    obtain ⟨b', hb', hby⟩ := Finset.mem_image.mp (Finset.mem_product.mp y.2).2
    let px : ↑(A ×ˢ B) := ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩
    let py : ↑(A ×ˢ B) := ⟨(a', b'), Finset.mem_product.mpr ⟨ha', hb'⟩⟩
    have hp : px = py := hTiles.1 (by
      apply e.injective
      simpa [px, py, sumMap, map_add, hax, hbx, hay, hby] using hxy)
    apply Subtype.ext
    apply Prod.ext
    · rw [← hax, ← hay]
      exact congrArg (fun p : ↑(A ×ˢ B) ↦ e p.1.1) hp
    · rw [← hbx, ← hby]
      exact congrArg (fun p : ↑(A ×ˢ B) ↦ e p.1.2) hp
  · intro g
    obtain ⟨p, hp⟩ := hTiles.2 (e.symm g)
    refine ⟨⟨(e p.1.1, e p.1.2), Finset.mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨p.1.1, (Finset.mem_product.mp p.2).1, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨p.1.2, (Finset.mem_product.mp p.2).2, rfl⟩
    · simpa [sumMap, ← map_add] using congrArg e hp

end Fuglede
