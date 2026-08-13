import Fuglede.Z180K30CertificateClosure
import Fuglede.Z180MasterConditionalClosure

/-!
# Master adapter for the cardinality-thirty certificate

This leaf is deliberately separated from the K30 proof cone so that the
already sealed master reduction need not be rebuilt while developing the
arithmetic certificate.
-/

namespace Fuglede

/-- Packaged form expected by the master `ZMod 180` closure. -/
theorem z180K30SpectralTilingClosure_of_orderClosureCertificate
    (hcert : Z180K30JointQFLIAOrderClosureCertificate) :
    Z180K30SpectralTilingClosure := by
  intro A L hSpec hcard
  exact z180_k30_exists_tiling_of_orderClosureCertificate
    hcert hSpec hcard

#print axioms z180K30SpectralTilingClosure_of_orderClosureCertificate

end Fuglede
