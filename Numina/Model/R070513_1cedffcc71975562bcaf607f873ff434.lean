import Mathlib

theorem algebra_199689 {x y : ℕ} (hy : y ≠ 0) (h1 : x * 5 = y * 7) (h2 : x * 3 = (y - 1) * 5) :
    x + y = 25 := by
  omega