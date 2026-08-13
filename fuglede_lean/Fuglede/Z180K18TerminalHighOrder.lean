import Fuglede.Z180K18TerminalInterface
import Fuglede.Z180K18DescentHighOrderKernels

/-!
# Table-free terminal branches at orders eighteen and thirty-six

The characteristic-five projection kernels rule out the two highest
five-factor defects directly.  This file only adapts those contradictions
to the honest terminal-branch interface.
-/

namespace Fuglede

private theorem z180_k18_cast36_injOn
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)) := by
  have hinj := z180_k18_projection36_injOn hSpec hcard
  intro x hx y hy hxy
  apply hinj hx hy
  simpa only [z180K18Projection36_apply] using hxy

/-- The `Phi_90`/not-`Phi_18` terminal defect is impossible after the
injective projection to `ZMod 36`. -/
theorem z180_k18_terminal_branch_eighteen :
    Z180K18TerminalBranchCertificate 18 := by
  intro A L hSpec hcard _ hdefect
  rcases hdefect with
    ⟨l₁, hl₁, l₂, hl₂, hne, hbaseOrder, hhighOrder, hhigh, hlow⟩
  have hfalse : False :=
    Z180K18HighOrder.z180_k18_descent_order18_kernel
      (z180_k18_cast36_injOn hSpec hcard)
      (by simpa using hhigh)
      (by simpa using hlow)
  exact hfalse.elim

/-- The `Phi_180`/not-`Phi_36` terminal defect is impossible after the
injective projection to `ZMod 36`. -/
theorem z180_k18_terminal_branch_thirtysix :
    Z180K18TerminalBranchCertificate 36 := by
  intro A L hSpec hcard _ hdefect
  rcases hdefect with
    ⟨l₁, hl₁, l₂, hl₂, hne, hbaseOrder, hhighOrder, hhigh, hlow⟩
  have hfalse : False :=
    Z180K18HighOrder.z180_k18_descent_order36_kernel
      (z180_k18_cast36_injOn hSpec hcard)
      (by simpa using hhigh)
      (by simpa using hlow)
  exact hfalse.elim

/-- The two terminal branches removed without an envelope or clique
certificate. -/
theorem z180_k18_terminal_high_order_branches :
    Z180K18TerminalBranchCertificate 18 ∧
      Z180K18TerminalBranchCertificate 36 :=
  ⟨z180_k18_terminal_branch_eighteen,
    z180_k18_terminal_branch_thirtysix⟩

#print axioms z180_k18_terminal_branch_eighteen
#print axioms z180_k18_terminal_branch_thirtysix
#print axioms z180_k18_terminal_high_order_branches

end Fuglede
