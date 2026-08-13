import Fuglede.K1CollisionCompactCore62Linarith
import Fuglede.K1CollisionCompactShardedAdapter

namespace Fuglede

theorem collisionUnsatAt_1_from_k1CollisionCompactShardedCore : CollisionUnsatAt 1 (axisSupportOfMask 0) :=
  collisionUnsatAt_1_of_k1CollisionCompactShardedRawCertificate (by
    intro a z
    exact fuglede_k1_collision_side0_compact a z)

#print axioms collisionUnsatAt_1_from_k1CollisionCompactShardedCore

end Fuglede
