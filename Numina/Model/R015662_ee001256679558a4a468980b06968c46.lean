import Mathlib

open Real

theorem inequalities_236134 (a b c : ℝ) (ha : a ≠ 0) (hroots : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0) :
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 9 / 8 * a ^ 2 := by
  rcases hroots with ⟨x, hx⟩
  have h1 : c = -a * x^2 - b * x := by linarith
  rw [h1]
  nlinarith [sq_nonneg (b + 2 * a * x), sq_nonneg (b - 2 * a * x), sq_nonneg (a * (x) + b / 2), sq_nonneg (b + a), sq_nonneg (b - 2 * a), sq_nonneg (a * x + b / 2), sq_nonneg (x + 1), sq_nonneg (x * a), sq_nonneg (x * b), sq_nonneg (x * a * x), sq_nonneg (x * b * x), sq_nonneg (b + 2 * a), sq_nonneg (b - a), sq_nonneg (x * b * a), sq_nonneg ((b) ^ 2 - 4 * a * (-a * x ^ 2 - b * x)), sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_nonneg (x ^ 2 - 1)]