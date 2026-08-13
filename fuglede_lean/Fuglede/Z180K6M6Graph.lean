import Fuglede.FrequencyOrder

/-!
# The terminal compatibility graph in the `ZMod 180`, `k = 6`, `m = 6` branch

The exact branch classification leaves only Fourier-zero orders `30`, or
orders `4` and `30`.  This module kernel-checks the finite terminal fact that
the corresponding Cayley graph is triangle-free.  Thus it cannot contain the
six-point clique required by a spectrum of cardinality six.

The proof first maps every allowed difference to `ZMod 4 × ZMod 5`.  Order
four has coordinate type `(odd, 0)`, while order thirty has coordinate type
`(2, nonzero)`.  Triangle-freeness then follows by splitting those two types
at two normalized edges.  `frequencyOrder` is integer division by a gcd, so
the proposition contains no floating-point or complex-number computation.
-/

namespace Fuglede

/-- A nonzero difference whose additive order is one of the two orders left
by the exact `k = 6`, `m = 6` zero-profile classification. -/
def Z180K6M6AllowedDifference (d : ZMod 180) : Prop :=
  d ≠ 0 ∧ (frequencyOrder 180 d = 4 ∨ frequencyOrder 180 d = 30)

/-- The two CRT coordinates needed by the terminal graph argument. -/
def z180K6M6Coordinates (d : ZMod 180) : ZMod 4 × ZMod 5 :=
  (ZMod.cast d, ZMod.cast d)

/-- Coordinate shadow of an order-four or order-thirty difference. -/
def Z180K6M6AllowedCoordinates (d : ZMod 4 × ZMod 5) : Prop :=
  (((d.1 = 1 ∨ d.1 = 3) ∧ d.2 = 0) ∨ (d.1 = 2 ∧ d.2 ≠ 0))

@[simp]
theorem z180_k6_m6_coordinates_sub (x y : ZMod 180) :
    z180K6M6Coordinates (x - y) =
      z180K6M6Coordinates x - z180K6M6Coordinates y := by
  simp [z180K6M6Coordinates]

/-- Every allowed order has one of the two advertised coordinate shadows.
The proof derives gcd `45` or `6`, then checks respectively four or thirty
possible quotients of the canonical representative. -/
theorem z180_k6_m6_allowed_implies_allowed_coordinates :
    ∀ d : ZMod 180,
      Z180K6M6AllowedDifference d →
      Z180K6M6AllowedCoordinates (z180K6M6Coordinates d) := by
  intro d hd
  rcases hd with ⟨_, horder⟩
  have hrepr : (d.val : ZMod 180) = d := ZMod.natCast_zmod_val d
  have hgcd_dvd : Nat.gcd 180 d.val ∣ 180 := Nat.gcd_dvd_left 180 d.val
  have hcancel := Nat.div_mul_cancel hgcd_dvd
  rcases horder with horder | horder
  · unfold frequencyOrder at horder
    rw [horder] at hcancel
    have hgcd : Nat.gcd 180 d.val = 45 := by omega
    have hdvd : 45 ∣ d.val := by
      rw [← hgcd]
      exact Nat.gcd_dvd_right 180 d.val
    obtain ⟨k, hk⟩ := hdvd
    have hklt : k < 4 := by
      have := d.val_lt
      omega
    rw [← hrepr]
    interval_cases k
    all_goals norm_num [hk] at hgcd
    all_goals simp only [hk]
    all_goals
      unfold Z180K6M6AllowedCoordinates z180K6M6Coordinates
      decide
  · unfold frequencyOrder at horder
    rw [horder] at hcancel
    have hgcd : Nat.gcd 180 d.val = 6 := by omega
    have hdvd : 6 ∣ d.val := by
      rw [← hgcd]
      exact Nat.gcd_dvd_right 180 d.val
    obtain ⟨k, hk⟩ := hdvd
    have hklt : k < 30 := by
      have := d.val_lt
      omega
    rw [← hrepr]
    interval_cases k
    all_goals norm_num [hk] at hgcd
    all_goals simp only [hk]
    all_goals
      unfold Z180K6M6AllowedCoordinates z180K6M6Coordinates
      decide

/-- The coordinate-shadow graph has no normalized triangle.  This proof
splits the two edge types rather than enumerating the twenty-element product. -/
theorem z180_k6_m6_no_coordinate_triangle :
    ∀ a b : ZMod 4 × ZMod 5,
      Z180K6M6AllowedCoordinates a →
      Z180K6M6AllowedCoordinates b →
      ¬ Z180K6M6AllowedCoordinates (a - b) := by
  rintro ⟨a4, a5⟩ ⟨b4, b5⟩ ha hb hab
  simp only [Z180K6M6AllowedCoordinates, Prod.fst_sub, Prod.snd_sub] at ha hb hab
  rcases ha with ⟨(rfl | rfl), rfl⟩ | ⟨rfl, ha5⟩ <;>
    rcases hb with ⟨(rfl | rfl), rfl⟩ | ⟨rfl, hb5⟩ <;>
    rcases hab with ⟨(hc4 | hc4), hc5⟩ | ⟨hc4, hc5⟩ <;>
    norm_num at *
  all_goals
    first
    | exact ha5 hc5
    | exact hb5 hc5
    | exact (by decide : ¬ (_ = _)) hc4

/-- Reversing a difference preserves the allowed-order predicate. -/
theorem z180_k6_m6_allowed_neg (d : ZMod 180) :
    Z180K6M6AllowedDifference (-d) ↔ Z180K6M6AllowedDifference d := by
  unfold Z180K6M6AllowedDifference
  rw [frequencyOrder_neg (by norm_num)]
  simp only [neg_ne_zero]

/-- The normalized compatibility graph has no triangle through zero. -/
theorem z180_k6_m6_no_normalized_triangle (a b : ZMod 180)
    (ha : Z180K6M6AllowedDifference a)
    (hb : Z180K6M6AllowedDifference b) :
    ¬ Z180K6M6AllowedDifference (a - b) := by
  intro hab
  apply z180_k6_m6_no_coordinate_triangle
    (z180K6M6Coordinates a) (z180K6M6Coordinates b)
    (z180_k6_m6_allowed_implies_allowed_coordinates a ha)
    (z180_k6_m6_allowed_implies_allowed_coordinates b hb)
  rw [← z180_k6_m6_coordinates_sub]
  exact z180_k6_m6_allowed_implies_allowed_coordinates (a - b) hab

/-- Coordinate-free form: three pairwise-compatible vertices cannot exist. -/
theorem z180_k6_m6_graph_triangle_free (x y z : ZMod 180)
    (hxy : Z180K6M6AllowedDifference (x - y))
    (hxz : Z180K6M6AllowedDifference (x - z))
    (hyz : Z180K6M6AllowedDifference (y - z)) : False := by
  apply z180_k6_m6_no_normalized_triangle (x - y) (x - z) hxy hxz
  have hzy : Z180K6M6AllowedDifference (z - y) := by
    simpa only [neg_sub] using (z180_k6_m6_allowed_neg (y - z)).2 hyz
  simpa only [sub_sub_sub_cancel_left] using hzy

end Fuglede
