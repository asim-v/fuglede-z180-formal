import Fuglede.K242CompactCore70Linarith
import Fuglede.K242CompactShardedAdapter

/-! # End-to-end certified contradiction at `k = 242`

This solver-free composition step identifies the compact 70-premise
arithmetic theorem with the proposition expected by the typed, sharded
adapter.  The adapter then discharges the mathematical interface
`BaseUnsatAt 242`.

The selected core is pinned to the full `k242.smt2` source SHA-256
`8ef32ff1e169a1bd2c3f7dbe07c739993639ee87ab78d35813519eaf65f7bab3`
and core-index SHA-256
`ac5b4df4ed85709474c11538854fbeee0a713b38e531a02f9cfd484e93a5d57b`.
-/

namespace Fuglede

/-- The pinned `k242` arithmetic certificate rules out the typed base system. -/
theorem baseUnsatAt_242 : BaseUnsatAt 242 :=
  baseUnsatAt_242_of_k242CompactShardedRawCertificate (by
    simpa only [K242CompactShardedRawCertificate] using
      fuglede_k242_core70_compact)

#print axioms baseUnsatAt_242

end Fuglede
