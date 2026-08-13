import Fuglede.Z180K30SixLevelFourierV4

namespace Fuglede

def z36K30Projection6 : ZMod 36 →+ ZMod 6 :=
  (ZMod.castHom (by norm_num : 6 ∣ 36) (ZMod 6)).toAddMonoidHom

@[simp]
theorem z36K30Projection6_apply (x : ZMod 36) :
    z36K30Projection6 x = ZMod.cast x := rfl

def Z180K30HCosetColumnConcrete
    (L : Finset (ZMod 180)) (s : Fin 5) : Prop :=
  ∃ ρ : ZMod 6,
    z180K30FifthFibres36 L s =
      (Finset.univ : Finset (ZMod 36)).filter
        (fun q ↦ z36K30Projection6 q = ρ)

def Z180K30AllHCosetColumnsConcrete (L : Finset (ZMod 180)) : Prop :=
  ∀ s : Fin 5, Z180K30HCosetColumnConcrete L s

def Z180K30Projection30Saturated (L : Finset (ZMod 180)) : Prop :=
  ∀ l ∈ L, ∀ b : ZMod 6, l + z180K30Kernel30Lift b ∈ L

def z180K30FinOfZMod5 (c : ZMod 5) : Fin 5 :=
  ⟨c.val, c.val_lt⟩

@[simp]
theorem z180K30FinOfZMod5_cast (c : ZMod 5) :
    ((z180K30FinOfZMod5 c).val : ZMod 5) = c := by
  exact ZMod.natCast_zmod_val c

set_option maxRecDepth 100000 in
theorem z180K30_kernel30Lift_preserves_H_coordinates :
    ∀ l : ZMod 180, ∀ b : ZMod 6,
      (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 5) = ZMod.cast l ∧
      z36K30Projection6
          (ZMod.cast (l + z180K30Kernel30Lift b) : ZMod 36) =
        z36K30Projection6 (ZMod.cast l : ZMod 36) := by
  intro l
  fin_cases l <;> decide

theorem z180K30_kernel30Lift_of_projection30_eq_zero :
    ∀ d : ZMod 180, z180K30Projection30 d = 0 →
      ∃ b : ZMod 6, d = z180K30Kernel30Lift b := by
  intro d
  fin_cases d <;> decide

theorem z180K30_projection30_eq_iff_exists_kernel30Lift
    (x y : ZMod 180) :
    z180K30Projection30 x = z180K30Projection30 y ↔
      ∃ b : ZMod 6, x = y + z180K30Kernel30Lift b := by
  constructor
  · intro hxy
    have hzero : z180K30Projection30 (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨b, hb⟩ :=
      z180K30_kernel30Lift_of_projection30_eq_zero (x - y) hzero
    refine ⟨b, ?_⟩
    have := congrArg (fun z : ZMod 180 ↦ z + y) hb
    simpa only [sub_add_cancel, add_comm] using this
  · rintro ⟨b, rfl⟩
    simp only [map_add, z180K30Projection30_kernel30Lift, add_zero]

theorem z180K30_kernel30_translate_injective
    (y : ZMod 180) :
    Function.Injective (fun b : ZMod 6 ↦ y + z180K30Kernel30Lift b) := by
  intro b₁ b₂ h
  apply z180K30Kernel30Lift_injective
  exact add_left_cancel h

#print axioms z180K30_projection30_eq_iff_exists_kernel30Lift

end Fuglede
