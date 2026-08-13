import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UBase

/-!
Direct completeness certificate for the eleven divisor-three U candidates.
The left-hand list is the exact profile-member order used by V97; the right
side is the actual deduplicated V89 normalized enumeration.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3UCanonicalNamedPilotV97 : List RawSet :=
  [z180K30ProfileV97D3U00M0000,
   z180K30ProfileV97D3U00M0001,
   z180K30ProfileV97D3U00M0002,
   z180K30ProfileV97D3U00M0003,
   z180K30ProfileV97D3U01M0000,
   z180K30ProfileV97D3U01M0001,
   z180K30ProfileV97D3U02M0000,
   z180K30ProfileV97D3U02M0001,
   z180K30ProfileV97D3U03M0000,
   z180K30ProfileV97D3U03M0001,
   z180K30ProfileV97D3U04M0000]

theorem z180_k30_projective_d3_u_source_named_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3USourceGrouped =
      z180K30ProjectiveD3UCanonicalNamedPilotV97 := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_u_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.Perm
      (normalizedProjectiveUniqueUChoicesV89 3) := by
  decide

#print axioms z180_k30_projective_d3_u_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
