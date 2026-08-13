import Fuglede.ExactOrderDistribution
import Fuglede.Z180DivisorCases
import Fuglede.Z180K12M6Elementary
import Fuglede.Z180K12M6SemanticOrders3_12
import Fuglede.Z180K12M6SemanticOrders
import Fuglede.Z180K12M6Order20Semantic
import Fuglede.Z180K12M6HighOrderSemanticHigh
import Mathlib.Tactic

/-!
# Unconditional exact zero sieve in the cardinality-twelve defect branch

Every nonzero frequency order divides `180`.  The elementary exclusions, the
sealed low/projected-order adapters, the exact order-twenty adapter, and the
five high-order adapters exhaust that divisor list.  Only orders
`2`, `4`, `10`, and `30` remain, exactly the safe envelope required by the
graph endpoint.
-/

namespace Fuglede

open Polynomial

/-- Kernel-checked implementation of the exact zero-sieve interface. -/
theorem z180_k12_m6_exact_zero_sieve : Z180K12M6ExactZeroSieve := by
  intro A hcard hinj htransform2 htransform4 hdefect d hdne hzero
  have hthreeTwelve := z180_k12_m6_cyclotomicZero_order_ne_three_twelve
    hcard hinj htransform2 htransform4 hdefect hzero
  have hnineEighteenThirtysix :=
    z180_k12_m6_cyclotomicZero_order_ne_nine_eighteen_thirtysix
      hcard hinj htransform2 htransform4 hdefect hzero
  have hhigh :=
    Z180K12HighOrder.z180_k12_m6_cyclotomicZero_order_ne_high_five
      hcard hinj htransform2 htransform4 hdefect hzero
  have hgt : 1 < frequencyOrder 180 d :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hdne
  have hdvd : frequencyOrder 180 d ∣ 180 :=
    frequencyOrder_dvd_modulus d
  rcases dvd_180_cases (by omega) hdvd with
    h1 | h2 | h3 | h4 | h5 | h6 | h9 | h10 | h12 | h15 | h18 |
      h20 | h30 | h36 | h45 | h60 | h90 | h180
  · omega
  · exact ⟨hdne, Or.inl h2⟩
  · exact False.elim (hthreeTwelve.1 h3)
  · exact ⟨hdne, Or.inr (Or.inl h4)⟩
  · exact False.elim (z180_k12_no_order5_zero hcard h5 hzero)
  · exact False.elim
      (z180_k12_no_order6_zero hdefect.2.1 h6 hzero)
  · exact False.elim (hnineEighteenThirtysix.1 h9)
  · exact ⟨hdne, Or.inr (Or.inr (Or.inl h10))⟩
  · exact False.elim (hthreeTwelve.2 h12)
  · exact False.elim (hhigh.1 h15)
  · exact False.elim (hnineEighteenThirtysix.2.1 h18)
  · apply False.elim
    apply z180_k12_m6_not_cyclotomic_twenty
      hcard hinj htransform2 htransform4 hdefect
    simpa [CyclotomicZero, h20] using hzero
  · exact ⟨hdne, Or.inr (Or.inr (Or.inr h30))⟩
  · exact False.elim (hnineEighteenThirtysix.2.2 h36)
  · exact False.elim (hhigh.2.1 h45)
  · exact False.elim (hhigh.2.2.1 h60)
  · exact False.elim (hhigh.2.2.2.1 h90)
  · exact False.elim (hhigh.2.2.2.2 h180)

#print axioms z180_k12_m6_exact_zero_sieve

end Fuglede
