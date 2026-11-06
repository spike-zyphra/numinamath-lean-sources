import Mathlib

theorem algebra_120903 (a b c : ℝ) (h : ∃ x y z : ℝ, a^2 + b^2 + c^2 + 3 * (x^2 + y^2 + z^2) = 6 ∧ a * x + b * y + c * z = 2) :
    False := by
  rcases h with ⟨x, y, z, h1, h2⟩
  nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (c - z),
          sq_nonneg (a * y - b * x), sq_nonneg (b * z - c * y), sq_nonneg (c * x - a * z),
          sq_nonneg (a * z - c * x), sq_nonneg (b * x - a * y), sq_nonneg (c * y - b * z)]