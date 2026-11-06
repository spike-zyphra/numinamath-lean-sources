import Mathlib

theorem inequalities_119484 (x y : ℝ) : 5*x^2+5*y^2+8*x*y+2*y-2*x+2≥0 := by
  nlinarith [sq_nonneg (x + (8 * y - 2) / 10), sq_nonneg (y + 1),
          sq_nonneg (5 * x + 4 * y - 1), sq_nonneg (4 * x + 5 * y + 1),
          sq_nonneg (x - y - 1), sq_nonneg (x + y + 1)]