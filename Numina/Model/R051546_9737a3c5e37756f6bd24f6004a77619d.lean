import Mathlib

theorem algebra_134944 {x y : ℕ} (hy : y ≠ 0) (h1 : (x + 2) * 60 = y * 90) (h2 : (x - 2) * 90 = y * 60) :
    y = 10 := by
  omega