import Mathlib

theorem inequalities_597379 (a b c : ℝ) (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ 0)
    (h₁ : a + b + c = 3) :
    a * b^2 + b * c^2 + c * a^2 ≤ 27 / 8 := by
  rcases h₀ with ⟨h₃, h₄, h₅⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 3 / 2),
          h₁, mul_nonneg (show b ≥ 0 by linarith) (show c ≥ 0 by linarith),
          mul_nonneg (show a ≥ 0 by linarith) (show b ≥ 0 by linarith),
          mul_nonneg (show a ≥ 0 by linarith) (show c ≥ 0 by linarith),
          h₃, h₄, h₅]