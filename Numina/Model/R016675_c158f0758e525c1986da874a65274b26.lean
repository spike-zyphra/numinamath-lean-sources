import Mathlib

theorem algebra_190176 (p q : ℝ) (h : ∃ x y, x > 2 ∧ y < 0 ∧ x^2 + 2 * p * x + q = 0 ∧ y^2 + 2 * p * y + q = 0) :
    q < 0 ∧ q < -4 - 4 * p := by
  rcases h with ⟨x, y, hx, hy, h1, h2⟩
  constructor
  · -- Prove that q < 0.
    nlinarith [sq_pos_of_pos (show x > 0 by linarith), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y + 2 * p), sq_nonneg (x - 2), sq_nonneg (y + 2 * p)]
  · -- Prove that q < -4 - 4 * p.
    nlinarith [sq_pos_of_pos (show x - 2 > 0 by linarith), sq_pos_of_neg (show y < 0 by linarith), sq_nonneg (x - y), sq_nonneg (x + 2 * p), sq_nonneg (y + 2 * p), sq_nonneg (x + y + 2 * p), sq_nonneg (x - 2), sq_nonneg (y + 2 * p)]