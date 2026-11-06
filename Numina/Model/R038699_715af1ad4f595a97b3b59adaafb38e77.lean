import Mathlib

theorem inequalities_87153 (a b c : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  have h3 : 0 ≤ b - a := by linarith
  have h4 : 0 ≤ c - b := by linarith
  have h5 : 0 ≤ c - a := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b - a by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c - b by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c - a by linarith),
            mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
            mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - a by linarith),
            mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ c - a by linarith),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)
          ]