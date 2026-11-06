import Mathlib

theorem inequalities_603672 (a b c : ℝ) (h₀ : a + b + c = 0) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 3 ≥ 6 * a * b * c := by
  have h1 : c = -a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 1), sq_nonneg (a + b - 1),
          sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (b - 1),
          sq_nonneg (a + b + a), sq_nonneg (a + b + b),
          sq_nonneg (a * b +1), sq_nonneg ((a + b) * a), sq_nonneg ((a + b) * b), sq_nonneg (a * b - (a + b) * 1)
          ]