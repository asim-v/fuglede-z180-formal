import Fuglede.Z180K18M6GraphDefs

/-!
# Local fibre kernels for the cardinality-eighteen `m = 6` graph

The leaves below are finite statements on `ZMod 4 × ZMod 9`.  They encode
the two elementary observations used by the structural proof: a same-level
triangle is vertical, and two mutually compatible double fibres are vertical
with opposite parities.
-/

namespace Fuglede

private def origin : Z180K18M6BaseCoord := 0

theorem z180_k18_m6_same_translate :
    ∀ t x y : Z180K18M6BaseCoord,
      Z180K18M6SameLevelCompatible x y ↔
        Z180K18M6SameLevelCompatible (x - t) (y - t) := by
  rintro ⟨t₄, t₉⟩ ⟨x₄, x₉⟩ ⟨y₄, y₉⟩
  simp [Z180K18M6SameLevelCompatible, z180K18M6Parity,
    sub_eq_add_neg]

theorem z180_k18_m6_cross_translate :
    ∀ t x y : Z180K18M6BaseCoord,
      Z180K18M6CrossLevelCompatible x y ↔
        Z180K18M6CrossLevelCompatible (x - t) (y - t) := by
  rintro ⟨t₄, t₉⟩ ⟨x₄, x₉⟩ ⟨y₄, y₉⟩
  simp [Z180K18M6CrossLevelCompatible, z180K18M6Parity,
    z180K18M6Third, sub_eq_add_neg]

theorem z180_k18_m6_cross_ninth_eq_of_opposite_parity_same_third
    {x y : Z180K18M6BaseCoord}
    (hcross : Z180K18M6CrossLevelCompatible x y)
    (hparity : z180K18M6Parity x ≠ z180K18M6Parity y)
    (hthird : z180K18M6Third x = z180K18M6Third y) :
    x.2 = y.2 := by
  rcases hcross with hsame | hopp
  · exact (hparity hsame.1).elim
  · exact hopp.2.resolve_right (not_ne_iff.mpr hthird)

/-- A normalized three-point clique in one fifth-coordinate fibre has a
constant modulo-four coordinate. -/
theorem z180_k18_m6_same_level_triangle_vertical :
    ∀ p q : Z180K18M6BaseCoord,
      p ≠ origin → q ≠ origin → p ≠ q →
      Z180K18M6SameLevelCompatible origin p →
      Z180K18M6SameLevelCompatible origin q →
      Z180K18M6SameLevelCompatible p q →
      p.1 = 0 ∧ q.1 = 0 := by
  letI : Decidable
      (∀ p q : Z180K18M6BaseCoord,
        p ≠ origin → q ≠ origin → p ≠ q →
        Z180K18M6SameLevelCompatible origin p →
        Z180K18M6SameLevelCompatible origin q →
        Z180K18M6SameLevelCompatible p q →
        p.1 = 0 ∧ q.1 = 0) :=
    Fintype.decidableForallFintype
  decide

/-- Translation-free form of the same-level triangle leaf. -/
theorem z180_k18_m6_same_level_triangle_vertical_general
    (x p q : Z180K18M6BaseCoord)
    (hxp : x ≠ p) (hxq : x ≠ q) (hpq : p ≠ q)
    (hxpSame : Z180K18M6SameLevelCompatible x p)
    (hxqSame : Z180K18M6SameLevelCompatible x q)
    (hpqSame : Z180K18M6SameLevelCompatible p q) :
    x.1 = p.1 ∧ x.1 = q.1 := by
  have h := z180_k18_m6_same_level_triangle_vertical
    (p - x) (q - x)
  have hpx : p - x ≠ origin := sub_ne_zero.mpr hxp.symm
  have hqx : q - x ≠ origin := sub_ne_zero.mpr hxq.symm
  have hpqx : p - x ≠ q - x := by
    intro heq
    exact hpq (sub_left_injective heq)
  have hsxp : Z180K18M6SameLevelCompatible origin (p - x) := by
    simpa [origin] using (z180_k18_m6_same_translate x x p).mp hxpSame
  have hsxq : Z180K18M6SameLevelCompatible origin (q - x) := by
    simpa [origin] using (z180_k18_m6_same_translate x x q).mp hxqSame
  have hspq := (z180_k18_m6_same_translate x p q).mp hpqSame
  specialize h hpx hqx hpqx hsxp hsxq hspq
  constructor
  · simpa using congrArg (fun z : ZMod 4 => z + x.1) h.1.symm
  · simpa using congrArg (fun z : ZMod 4 => z + x.1) h.2.symm

/-- A horizontal same-level pair has no point in another level compatible
with both endpoints. -/
theorem z180_k18_m6_horizontal_pair_blocks_cross_vertex :
    ∀ p q : Z180K18M6BaseCoord,
      p.2 = 0 → z180K18M6Parity p ≠ 0 →
      ¬ (Z180K18M6CrossLevelCompatible origin q ∧
         Z180K18M6CrossLevelCompatible p q) := by
  decide

/-- If two two-point fibres are completely cross-compatible, both pairs are
vertical and their modulo-four parities are opposite. -/
theorem z180_k18_m6_compatible_double_fibres :
    ∀ p q r : Z180K18M6BaseCoord,
      p ≠ origin → q ≠ r →
      Z180K18M6SameLevelCompatible origin p →
      Z180K18M6SameLevelCompatible q r →
      Z180K18M6CrossLevelCompatible origin q →
      Z180K18M6CrossLevelCompatible origin r →
      Z180K18M6CrossLevelCompatible p q →
      Z180K18M6CrossLevelCompatible p r →
      p.1 = 0 ∧ q.1 = r.1 ∧ z180K18M6Parity q ≠ 0 := by
  decide

/-- Translation-free form of the preceding normalized leaf. -/
theorem z180_k18_m6_compatible_double_fibres_general
    (x p q r : Z180K18M6BaseCoord)
    (hxp : x ≠ p) (hqr : q ≠ r)
    (hxpSame : Z180K18M6SameLevelCompatible x p)
    (hqrSame : Z180K18M6SameLevelCompatible q r)
    (hxq : Z180K18M6CrossLevelCompatible x q)
    (hxr : Z180K18M6CrossLevelCompatible x r)
    (hpq : Z180K18M6CrossLevelCompatible p q)
    (hpr : Z180K18M6CrossLevelCompatible p r) :
    x.1 = p.1 ∧ q.1 = r.1 ∧
      z180K18M6Parity x ≠ z180K18M6Parity q := by
  have h := z180_k18_m6_compatible_double_fibres
    (p - x) (q - x) (r - x)
  have hpx : p - x ≠ origin := sub_ne_zero.mpr hxp.symm
  have hqrx : q - x ≠ r - x := by
    intro h
    exact hqr (sub_left_injective h)
  have hsxp : Z180K18M6SameLevelCompatible origin (p - x) := by
    simpa [origin] using
      (z180_k18_m6_same_translate x x p).mp hxpSame
  have hsqr : Z180K18M6SameLevelCompatible (q - x) (r - x) :=
    (z180_k18_m6_same_translate x q r).mp hqrSame
  have hcxq : Z180K18M6CrossLevelCompatible origin (q - x) := by
    simpa [origin] using (z180_k18_m6_cross_translate x x q).mp hxq
  have hcxr : Z180K18M6CrossLevelCompatible origin (r - x) := by
    simpa [origin] using (z180_k18_m6_cross_translate x x r).mp hxr
  have hcpq := (z180_k18_m6_cross_translate x p q).mp hpq
  have hcpr := (z180_k18_m6_cross_translate x p r).mp hpr
  specialize h hpx hqrx hsxp hsqr hcxq hcxr hcpq hcpr
  rcases h with ⟨hp, hqr', hpar⟩
  constructor
  · simpa using congrArg (fun z : ZMod 4 => z + x.1) hp.symm
  constructor
  · simpa using congrArg (fun z : ZMod 4 => z + x.1) hqr'
  · intro hxqParity
    apply hpar
    unfold z180K18M6Parity at hxqParity ⊢
    simpa using (sub_eq_zero.mpr hxqParity.symm)

/-- Three points in one level force every point compatible from another
level to have the opposite modulo-four parity. -/
theorem z180_k18_m6_triangle_forces_cross_parity :
    ∀ p q r : Z180K18M6BaseCoord,
      p ≠ origin → q ≠ origin → p ≠ q →
      Z180K18M6SameLevelCompatible origin p →
      Z180K18M6SameLevelCompatible origin q →
      Z180K18M6SameLevelCompatible p q →
      Z180K18M6CrossLevelCompatible origin r →
      Z180K18M6CrossLevelCompatible p r →
      Z180K18M6CrossLevelCompatible q r →
      p.1 = 0 ∧ q.1 = 0 ∧ z180K18M6Parity r ≠ 0 := by
  decide

/-- Translation-free form of the triangle-to-cross-parity leaf. -/
theorem z180_k18_m6_triangle_forces_cross_parity_general
    (x p q r : Z180K18M6BaseCoord)
    (hxp : x ≠ p) (hxq : x ≠ q) (hpq : p ≠ q)
    (hxpSame : Z180K18M6SameLevelCompatible x p)
    (hxqSame : Z180K18M6SameLevelCompatible x q)
    (hpqSame : Z180K18M6SameLevelCompatible p q)
    (hxr : Z180K18M6CrossLevelCompatible x r)
    (hpr : Z180K18M6CrossLevelCompatible p r)
    (hqr : Z180K18M6CrossLevelCompatible q r) :
    z180K18M6Parity x ≠ z180K18M6Parity r := by
  have h := z180_k18_m6_triangle_forces_cross_parity
    (p - x) (q - x) (r - x)
  have hpx : p - x ≠ origin := sub_ne_zero.mpr hxp.symm
  have hqx : q - x ≠ origin := sub_ne_zero.mpr hxq.symm
  have hpqx : p - x ≠ q - x := by
    intro heq
    exact hpq (sub_left_injective heq)
  have hsxp : Z180K18M6SameLevelCompatible origin (p - x) := by
    simpa [origin] using (z180_k18_m6_same_translate x x p).mp hxpSame
  have hsxq : Z180K18M6SameLevelCompatible origin (q - x) := by
    simpa [origin] using (z180_k18_m6_same_translate x x q).mp hxqSame
  have hspq := (z180_k18_m6_same_translate x p q).mp hpqSame
  have hcxr : Z180K18M6CrossLevelCompatible origin (r - x) := by
    simpa [origin] using (z180_k18_m6_cross_translate x x r).mp hxr
  have hcpr := (z180_k18_m6_cross_translate x p r).mp hpr
  have hcqr := (z180_k18_m6_cross_translate x q r).mp hqr
  specialize h hpx hqx hpqx hsxp hsxq hspq hcxr hcpr hcqr
  intro hxrParity
  apply h.2.2
  unfold z180K18M6Parity at hxrParity ⊢
  simpa using (sub_eq_zero.mpr hxrParity.symm)

#print axioms z180_k18_m6_same_level_triangle_vertical
#print axioms z180_k18_m6_same_level_triangle_vertical_general
#print axioms z180_k18_m6_horizontal_pair_blocks_cross_vertex
#print axioms z180_k18_m6_compatible_double_fibres
#print axioms z180_k18_m6_compatible_double_fibres_general
#print axioms z180_k18_m6_triangle_forces_cross_parity
#print axioms z180_k18_m6_triangle_forces_cross_parity_general

end Fuglede
