import Mathlib

theorem inequalities_46243 (x y z : ℝ) (h₀ : x + y + z = 3) :
    x * y + x * z + y * z ≤ 3 := by
  have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by
    nlinarith
  have h2 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 ≥ 0 := by
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h₀]