import Fuglede.Z180K12DescentOrder12Kernel
import Fuglede.Z180K12DescentOrder18Kernel
import Fuglede.Z180K12DescentOrder36Kernel

/-! # Direct assembly of the three mixed descent kernels -/

namespace Fuglede

open Z180K12HighOrder

/-- Kernel-checked direct replacement for the historical meet-in-the-middle
payload: base orders `12`, `18`, and `36` are all impossible. -/
theorem z180_k12_direct_mixed_descent_kernels :
    Z180K12MixedDescentKernels :=
  ⟨z180_k12_descent_order12_kernel,
    z180_k12_descent_order18_kernel,
    z180_k12_descent_order36_kernel⟩

#print axioms z180_k12_direct_mixed_descent_kernels

end Fuglede
