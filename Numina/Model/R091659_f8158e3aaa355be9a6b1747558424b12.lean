import Mathlib

theorem algebra_50161 {x : ℕ} (hx : x > 0) (h : 4 * x = x ^ 2 + 2 * (x + 1)) :
    x = 2 := by
  nlinarith [sq_nonneg (x : ℕ), sq_nonneg ((x : ℕ) - 2)]