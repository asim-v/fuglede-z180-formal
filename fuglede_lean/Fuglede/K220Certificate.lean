import Fuglede.K220Core72Linarith
import Fuglede.K220TypedAdapter

/-! # End-to-end certified contradiction at `k = 220`

This module is the final, solver-free composition step.  The pinned
72-assertion arithmetic proof has exactly the proposition expected by the
typed adapter, which turns it into the mathematical interface
`BaseUnsatAt 220`.
-/

namespace Fuglede

/-- The pinned `k220` arithmetic certificate rules out the typed base system. -/
theorem baseUnsatAt_220 : BaseUnsatAt 220 :=
  baseUnsatAt_220_of_k220RawCertificate (by
    simpa only [K220RawCertificate] using fuglede_k220_core72_linarith)

#print axioms baseUnsatAt_220

end Fuglede
