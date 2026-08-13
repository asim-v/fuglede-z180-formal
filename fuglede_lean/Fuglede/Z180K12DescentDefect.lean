import Fuglede.Z180K12DescentImages
import Fuglede.Z180K6DescentDefect

/-!
# A failed cardinality-twelve descent produces a five-factor defect

The generic projected-mask and frequency-order lemmas from the
cardinality-six descent are independent of cardinality.  Combined with the
cardinality-twelve injectivity gateway, they turn a failed projected zero
into a precise `Phi_(5m)`/not-`Phi_m` defect with `m | 36`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Exact algebraic shape of one failed projected zero at cardinality
twelve. -/
def Z180K12Projection36FiveFactorDefect
    (A L : Finset (ZMod 180)) : Prop :=
  ∃ l₁ ∈ L, ∃ l₂ ∈ L, l₁ ≠ l₂ ∧
    let m := frequencyOrder 36
      (z180K12Projection36 l₁ - z180K12Projection36 l₂)
    m ∣ 36 ∧ 1 < m ∧
      frequencyOrder 180 (l₁ - l₂) = 5 * m ∧
      cyclotomic (5 * m) Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic m Int ∣ maskPolynomial 180 A

/-- A failure of exact zero descent produces a five-factor cyclotomic defect
on the original mask. -/
theorem z180_k12_fiveFactorDefect_of_not_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12)
    (hnotdesc : ¬ Z180K12Projection36ZeroDescends A L) :
    Z180K12Projection36FiveFactorDefect A L := by
  classical
  simp only [Z180K12Projection36ZeroDescends, not_forall,
    _root_.not_imp] at hnotdesc
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hnotzero⟩ := hnotdesc
  let d : ZMod 180 := l₁ - l₂
  let d36 : ZMod 36 := z180K12Projection36 l₁ - z180K12Projection36 l₂
  let m : Nat := frequencyOrder 36 d36
  have hinjL := z180_k12_projection36_spectrum_injOn hSpec hcard
  have hd36ne : d36 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    exact hne (hinjL hl₁ hl₂ heq)
  have hmgt : 1 < m :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hd36ne
  have hm36 : m ∣ 36 := frequencyOrder_dvd_modulus d36
  have hinjA12 := z180_k12_projection36_injOn hSpec hcard
  have hinjA6 : Set.InjOn z180K6Projection36 (A : Set (ZMod 180)) := by
    simpa [z180K12Projection36, z180K6Projection36] using hinjA12
  have hnotlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A := by
    intro hlow
    apply hnotzero
    unfold CyclotomicZero
    change cyclotomic m Int ∣
      maskPolynomial 36 (A.image z180K12Projection36)
    rw [show A.image z180K12Projection36 =
        A.image z180K6Projection36 by
          simp [z180K12Projection36, z180K6Projection36]]
    rw [maskPolynomial_projection36_image_eq hinjA6]
    exact (cyclotomic_dvd_projection36Mask_iff_dvd_mask hm36).2 hlow
  have horiginal : CyclotomicZero 180 A d :=
    hSpec.2.2 l₁ hl₁ l₂ hl₂ hne
  have hmap : z180K6Projection36 d = d36 := by
    simp [d, d36, z180K12Projection36, z180K6Projection36, map_sub]
  have horderCases := z180_frequencyOrder_projection36_cases d
  rw [hmap] at horderCases
  have horderHigh : frequencyOrder 180 d = 5 * m := by
    rcases horderCases with heq | heq
    · exfalso
      apply hnotlow
      simpa [CyclotomicZero, d, m, heq] using horiginal
    · exact heq
  have hhigh : cyclotomic (5 * m) Int ∣ maskPolynomial 180 A := by
    simpa [CyclotomicZero, d, horderHigh] using horiginal
  exact ⟨l₁, hl₁, l₂, hl₂, hne, hm36, hmgt,
    horderHigh, hhigh, hnotlow⟩

/-- Conditional non-tiler endpoint; its sole smaller-modulus input is the
exact cardinality-twelve theorem in `ZMod 36`. -/
theorem z180_k12_fiveFactorDefect_of_non_tiler
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12)
    (hInduction : Z36SpectralCard12ImpliesTile)
    (hnot : ¬ ∃ B : Finset (ZMod 180), Tiles A B) :
    Z180K12Projection36FiveFactorDefect A L := by
  apply z180_k12_fiveFactorDefect_of_not_zero_descent hSpec hcard
  exact z180_k12_not_zero_descent_of_non_tiler
    hSpec hcard hInduction hnot

#print axioms z180_k12_fiveFactorDefect_of_not_zero_descent
#print axioms z180_k12_fiveFactorDefect_of_non_tiler

end Fuglede
