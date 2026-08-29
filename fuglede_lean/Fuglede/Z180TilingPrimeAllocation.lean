import Fuglede.FourierTiling
import Fuglede.PrimeCyclotomic
import Fuglede.Z180SmallCardinality
import Fuglede.Z180ExactOrderTransform
import Mathlib.Tactic

/-!
# Prime cyclotomic allocation in a finite tiling

At a frequency of prime order, the tiling zero cover says that one of the two
mask polynomials has the corresponding prime cyclotomic factor.  Evaluation
at one then forces that prime to divide the cardinality of that factor.  Thus
cardinality alone decides which side must carry the zero whenever exactly one
side is divisible by the prime.
-/

namespace Fuglede

/-- If the first factor of a tiling has cardinality not divisible by `p`, then
the second factor carries every specified nonzero zero of exact prime order
`p`. -/
theorem complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
    {N p : ℕ} [NeZero N] {A B : Finset (ZMod N)} {d : ZMod N}
    (hp : p.Prime) (horder : frequencyOrder N d = p) (hd : d ≠ 0)
    (hTiles : Tiles A B) (hnot : ¬ p ∣ A.card) :
    CyclotomicZero N B d := by
  rcases cyclotomic_zero_cover_of_tiles hTiles d hd with hA | hB
  · exact (hnot (prime_dvd_card_of_cyclotomicZero hp A d horder hA)).elim
  · exact hB

/-- Prime-power variant: a zero of exact order `p^(k+1)` on the first side
would still force `p` to divide its cardinality, so a nondivisible first side
allocates that zero to the complement. -/
theorem complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
    {N p k : ℕ} [NeZero N] {A B : Finset (ZMod N)} {d : ZMod N}
    (hp : p.Prime) (horder : frequencyOrder N d = p ^ (k + 1)) (hd : d ≠ 0)
    (hTiles : Tiles A B) (hnot : ¬ p ∣ A.card) :
    CyclotomicZero N B d := by
  rcases cyclotomic_zero_cover_of_tiles hTiles d hd with hA | hB
  · apply (hnot ?_).elim
    apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask hp k A
    simpa [CyclotomicZero, horder] using hA
  · exact hB

/-- Order-two allocation in `ZMod 180`. -/
theorem z180_complement_cyclotomicZero_two_of_tiles_of_odd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hodd : ¬ 2 ∣ A.card) :
    CyclotomicZero 180 B (90 : ZMod 180) := by
  apply complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
    (p := 2) (by norm_num) (by decide) (by decide) hTiles hodd

/-- Order-three allocation in `ZMod 180`. -/
theorem z180_complement_cyclotomicZero_three_of_tiles_of_not_three_dvd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬ 3 ∣ A.card) :
    CyclotomicZero 180 B (60 : ZMod 180) := by
  apply complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
    (p := 3) (by norm_num) (by decide) (by decide) hTiles hnot

/-- Order-five allocation in `ZMod 180`. -/
theorem z180_complement_cyclotomicZero_five_of_tiles_of_not_five_dvd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬ 5 ∣ A.card) :
    CyclotomicZero 180 B (36 : ZMod 180) := by
  apply complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
    (p := 5) (by norm_num) (by decide) (by decide) hTiles hnot

/-- Order-four allocation in `ZMod 180`. -/
theorem z180_complement_cyclotomicZero_four_of_tiles_of_odd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hodd : ¬ 2 ∣ A.card) :
    CyclotomicZero 180 B (45 : ZMod 180) := by
  apply complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
    (p := 2) (k := 1) (by norm_num) (by decide) (by decide) hTiles hodd

/-- Order-nine allocation in `ZMod 180`. -/
theorem z180_complement_cyclotomicZero_nine_of_tiles_of_not_three_dvd_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬ 3 ∣ A.card) :
    CyclotomicZero 180 B (20 : ZMod 180) := by
  apply complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
    (p := 3) (k := 1) (by norm_num) (by decide) (by decide) hTiles hnot

/-- The symmetric allocation rule for the first factor. -/
theorem z180_left_cyclotomicZero_five_of_tiles_of_not_five_dvd_right_card
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hnot : ¬ 5 ∣ B.card) :
    CyclotomicZero 180 A (36 : ZMod 180) := by
  exact z180_complement_cyclotomicZero_five_of_tiles_of_not_five_dvd_card
    (tiles_comm hTiles) hnot

/-- The full prime-power allocation forced by a `36 × 5` tiling.  This is the
`T1` part of the cardinality-thirty-six converse. -/
theorem z180_tile_card_thirty_six_primePower_zeros
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36) :
    CyclotomicZero 180 A (90 : ZMod 180) ∧
    CyclotomicZero 180 A (60 : ZMod 180) ∧
    CyclotomicZero 180 A (45 : ZMod 180) ∧
    CyclotomicZero 180 A (20 : ZMod 180) ∧
    CyclotomicZero 180 B (36 : ZMod 180) := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 5 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact z180_complement_cyclotomicZero_two_of_tiles_of_odd_card
      (tiles_comm hTiles) (by omega)
  · exact z180_complement_cyclotomicZero_three_of_tiles_of_not_three_dvd_card
      (tiles_comm hTiles) (by omega)
  · exact z180_complement_cyclotomicZero_four_of_tiles_of_odd_card
      (tiles_comm hTiles) (by omega)
  · exact z180_complement_cyclotomicZero_nine_of_tiles_of_not_three_dvd_card
      (tiles_comm hTiles) (by omega)
  · exact z180_complement_cyclotomicZero_five_of_tiles_of_not_five_dvd_card
      hTiles (by omega)

#print axioms complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
#print axioms z180_complement_cyclotomicZero_five_of_tiles_of_not_five_dvd_card
#print axioms z180_tile_card_thirty_six_primePower_zeros

end Fuglede
