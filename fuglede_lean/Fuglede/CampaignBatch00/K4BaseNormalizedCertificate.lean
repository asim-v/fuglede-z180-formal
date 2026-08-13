import Fuglede.CampaignBatch00.RawSmallBatch00
import Fuglede.CampaignBatch00.K4BaseNormalizedTypedAdapter

namespace Fuglede

theorem baseUnsatAt_4_from_k4BaseNormalizedCore : BaseUnsatAt 4 :=
  baseUnsatAt_4_of_k4BaseNormalizedRawCertificate (by
    simpa only [K4BaseNormalizedRawCertificate] using fuglede_k4_base_core_compact)

#print axioms baseUnsatAt_4_from_k4BaseNormalizedCore

end Fuglede
