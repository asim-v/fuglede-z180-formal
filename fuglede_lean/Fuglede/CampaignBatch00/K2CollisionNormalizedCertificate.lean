import Fuglede.CampaignBatch00.RawSmallBatch00
import Fuglede.CampaignBatch00.K2CollisionNormalizedTypedAdapter

namespace Fuglede

theorem collisionUnsatAt_2_from_k2CollisionNormalizedCore : CollisionUnsatAt 2 (axisSupportOfMask 1) :=
  collisionUnsatAt_2_of_k2CollisionNormalizedRawCertificate (by
    simpa only [K2CollisionNormalizedRawCertificate] using fuglede_k2_collision_static_core_compact)

#print axioms collisionUnsatAt_2_from_k2CollisionNormalizedCore

end Fuglede
