import Mathlib

theorem inequalities_119339 (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 4) :
    (2 + a) * (2 + b) ≥ c * d := by
  nlinarith [sq_nonneg (a + b + 2), sq_nonneg (c - d), sq_nonneg (c + d - (a + b)), sq_nonneg (a - b), sq_nonneg (c - d)]