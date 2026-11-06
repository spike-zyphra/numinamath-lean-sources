import Mathlib

theorem inequalities_173307 (x : ℝ) : x * (x + 1) * (x + 2) * (x + 3) ≥ -1 := by
  nlinarith [sq_nonneg (x ^ 2 + 3 * x + 1), sq_nonneg ((x + 3 / 2) ^ 2), sq_nonneg (x * (x + 3)), sq_nonneg (x + 3 / 2)]