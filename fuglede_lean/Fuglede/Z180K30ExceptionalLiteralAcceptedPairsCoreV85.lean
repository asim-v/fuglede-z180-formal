import Fuglede.Z180K30ExceptionalRawCoreV2

/-!
# Kernel-friendly literal pair payloads for the K30 projective catalogue

Each generated leaf evaluates only a small list of literal accepted pairs.
It never reconstructs a prefix of `choose`, `drop`, or the 159516-candidate
projective family.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def literalExceptionalPairCoveredB_v85
    (pair : RawSet × RawSet) : Bool :=
  exceptionalPairB pair.1 pair.2 &&
    (orbitCoveredB pair.1 && orbitCoveredB pair.2)

structure CertifiedLiteralAcceptedPairShardV85 where
  divisor : Nat
  supported_divisor :
    divisor = 3 ∨ divisor = 4 ∨ divisor = 6
  pairs : List (RawSet × RawSet)
  covered : pairs.all literalExceptionalPairCoveredB_v85 = true

end Fuglede.Z180K30ExceptionalRawV2
