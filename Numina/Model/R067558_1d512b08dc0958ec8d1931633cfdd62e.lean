import Mathlib

theorem algebra_3020 (x : ℝ) (hx : 0 < x) : abs (8 * x - 1) + 22 ≠ 20 := by
  intro h
  have h1 : abs (8 * x - 1) = -2 := by linarith
  have h2 : abs (8 * x - 1) ≥ 0 := abs_nonneg (8 * x - 1)
  linarith