import Fuglede.Z180K30FibreTiling
import Fuglede.Z180K30OrderClosureBridge

/-!
# Conditional `k = 30` tiling closure

This is the final structural adapter.  It contains no arithmetic proof: a
term of `Z180K30JointQFLIAOrderClosureCertificate` must come from the nine
materialized bad-signature certificates.  Given that term, the common
`ZMod 36` complement is reassembled into an exact tiling of `ZMod 180`.
-/

namespace Fuglede

/-- The arithmetic order-closure certificate closes one cardinality-thirty
spectral pair. -/
theorem z180_k30_exists_tiling_of_orderClosureCertificate
    (hcert : Z180K30JointQFLIAOrderClosureCertificate)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  let hzeroCert : Z180K30JointQFLIAZeroDescentCertificate :=
    z180K30JointQFLIAZeroDescentCertificate_of_orderClosureCertificate hcert
  obtain ⟨B, hB⟩ :=
    z180_k30_five_fibres_common_complement_of_joint_qflia_certificate
      hzeroCert hSpec hcard
  have hB' : ∀ c : ZMod 5, Tiles (z180K30Fibre A c) B := by
    intro c
    let i : Fin 5 := ⟨c.val, c.val_lt⟩
    have hi := hB i
    change Tiles (z180K30Fibre A (i.val : ZMod 5)) B at hi
    simpa only [i, ZMod.natCast_zmod_val] using hi
  exact ⟨z180K30LiftComplement B,
    z180_k30_tiles_of_common_fibre_complement A B hB'⟩

end Fuglede
