import Fuglede.CyclicCertificate

/-!
# A fiber-capacity obstruction for cyclotomic spectra

Suppose a map `f : ZMod N → β` has the property that two distinct candidate
frequencies in the same fiber can never have the cyclotomic zero required of
a spectrum.  Spectrality then forces `f` to be injective on the spectrum, so
the spectrum—and hence the spectral set—has cardinality at most `|β|`.

This packages a common finite reduction: after proving a local obstruction
inside each CRT fiber, cardinality alone can rule out an alleged spectrum.
-/

namespace Fuglede

/-- A same-fiber obstruction to cyclotomic zeros bounds the size of a spectral
set by the number of fibers. -/
theorem card_le_card_fibers_of_cyclotomicSpectrum
    {N : ℕ} {β : Type*} [Fintype β]
    (A L : Finset (ZMod N)) (f : ZMod N → β)
    (hforbid : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → f x = f y →
      ¬CyclotomicZero N A (x - y))
    (hSpec : CyclotomicSpectrum N A L) :
    A.card ≤ Fintype.card β := by
  classical
  have hf_inj : Set.InjOn f (L : Set (ZMod N)) := by
    intro x hx y hy hxy
    by_contra hne
    exact (hforbid x hx y hy hne hxy) (hSpec.2.2 x hx y hy hne)
  rw [hSpec.2.1]
  simpa using
    (Finset.card_le_card_of_injOn f
      (s := L) (t := (Finset.univ : Finset β))
      (fun _ _ => Finset.mem_univ _) hf_inj)

/-- If there are fewer fibers than elements of `A`, the same local
obstruction certifies that `L` cannot be a cyclotomic spectrum for `A`. -/
theorem not_cyclotomicSpectrum_of_card_fibers_lt
    {N : ℕ} {β : Type*} [Fintype β]
    (A L : Finset (ZMod N)) (f : ZMod N → β)
    (hforbid : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → f x = f y →
      ¬CyclotomicZero N A (x - y))
    (hcard : Fintype.card β < A.card) :
    ¬CyclotomicSpectrum N A L := by
  intro hSpec
  exact (Nat.not_le_of_lt hcard)
    (card_le_card_fibers_of_cyclotomicSpectrum A L f hforbid hSpec)

end Fuglede
