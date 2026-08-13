import Mathlib.Tactic

example (a b : Int) (h : a > 0 → b = 0) (ha : a > 0) (hb : b > 0) : False := by
  omega
