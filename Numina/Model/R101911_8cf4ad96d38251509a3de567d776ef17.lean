import Mathlib

theorem algebra_227912 (x : ℕ) (hx : x ≤ 4) (h : 10 * x + 90 = 9 * x + 7 * (4 - x) + 8 * (4 - x) + 9 * (4 - x)) :
    x = 3 := by
  omega