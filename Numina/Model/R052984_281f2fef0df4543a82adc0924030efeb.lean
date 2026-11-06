import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_258341 {a b : ℝ} (ha : 0 ≤ a) (hb : a ≤ b)
  (h : b - 1014 ≤ b) (h' : a ≤ b - 1981) :
  (b - 1014 - a + 1981) ≥ 983 := by
    linarith