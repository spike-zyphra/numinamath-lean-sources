import Mathlib

theorem algebra_143360 {x : ℕ} (hx : x > 0) (h : 100 * (x / 2) + 200 * (x / 2 - 5) = 180 * x) :
    x = 180 := by
  omega