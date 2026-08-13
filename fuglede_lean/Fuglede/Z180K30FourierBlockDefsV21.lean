import Fuglede.Z180K30FiveBlockGramDataV20
import Fuglede.Z180K30FibreFourier
import Mathlib.Data.Finset.Sort

/-! Canonical enumerations and six-by-six Fourier blocks of the K30 fibres. -/

namespace Fuglede

noncomputable section

structure Z180K30BalancedFibreDataV21
    (A L : Finset (ZMod 180)) : Prop where
  cardA : ∀ r : Fin 5, (z180K30FifthFibres36 A r).card = 6
  cardL : ∀ s : Fin 5, (z180K30FifthFibres36 L s).card = 6

def z180K30BalancedFibreDataV21_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    Z180K30BalancedFibreDataV21 A L where
  cardA r := z180_k30_fibre_card_six hSpec hcard (r.val : ZMod 5)
  cardL s := z180_k30_fibre_card_six
    (cyclotomicSpectrum_dual hSpec) (hSpec.2.1.symm.trans hcard)
      (s.val : ZMod 5)

noncomputable def z180K30FibreEnumV21
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Fin 6 -> ZMod 36 :=
  fun k => (Finset.orderIsoOfFin (z180K30FifthFibres36 X i) hcard k).1

theorem z180K30FibreEnumV21_mem
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) (k : Fin 6) :
    z180K30FibreEnumV21 X i hcard k ∈ z180K30FifthFibres36 X i :=
  (Finset.orderIsoOfFin (z180K30FifthFibres36 X i) hcard k).2

theorem z180K30FibreEnumV21_injective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    Function.Injective (z180K30FibreEnumV21 X i hcard) := by
  intro k l hkl
  apply (Finset.orderIsoOfFin (z180K30FifthFibres36 X i) hcard).injective
  exact Subtype.ext hkl

theorem z180K30FibreEnumV21_surjective
    (X : Finset (ZMod 180)) (i : Fin 5)
    (hcard : (z180K30FifthFibres36 X i).card = 6) :
    ∀ x ∈ z180K30FifthFibres36 X i,
      ∃ k : Fin 6, z180K30FibreEnumV21 X i hcard k = x := by
  intro x hx
  obtain ⟨k, hk⟩ :=
    (Finset.orderIsoOfFin (z180K30FifthFibres36 X i) hcard).surjective
      ⟨x, hx⟩
  refine ⟨k, ?_⟩
  exact congrArg Subtype.val hk

noncomputable def z180K30FourierBlockV21
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV21 A L)
    (r s : Fin 5) : Z180K30BlockMatrixV19 :=
  Matrix.of fun a l => ZMod.stdAddChar
    (z180K30FibreEnumV21 A r (data.cardA r) a *
      z180K30FibreEnumV21 L s (data.cardL s) l)

@[simp]
theorem z180K30FourierBlockV21_apply
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV21 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30FourierBlockV21 data r s a l = ZMod.stdAddChar
      (z180K30FibreEnumV21 A r (data.cardA r) a *
        z180K30FibreEnumV21 L s (data.cardL s) l) := rfl

theorem z180K30FourierBlockV21_entry_ne_zero
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV21 A L)
    (r s : Fin 5) (a l : Fin 6) :
    z180K30FourierBlockV21 data r s a l ≠ 0 := by
  rw [z180K30FourierBlockV21_apply, ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

#print axioms z180K30BalancedFibreDataV21_of_spectral
#print axioms z180K30FibreEnumV21_surjective
#print axioms z180K30FourierBlockV21_entry_ne_zero

end
end Fuglede
