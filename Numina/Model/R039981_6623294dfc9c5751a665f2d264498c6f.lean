import Mathlib

theorem algebra_193805 {a b c d : ℝ} (h : a^2 + b^2 + c^2 + d^2 - a * b - b * c - c * d - d + 2 / 5 = 0) :
    a = 1 / 5 ∧ b = 2 / 5 ∧ c = 3 / 5 ∧ d = 4 / 5 := by

  have h1 : (d - 4 / 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1 / 5 : ℝ), sq_nonneg (b - 2 / 5 : ℝ), sq_nonneg (c - 3 / 5 : ℝ), sq_nonneg (d - 4 / 5 : ℝ),
          sq_nonneg (a - b / 2 : ℝ), sq_nonneg (b - 2 * c / 3 : ℝ), sq_nonneg (c - 3 * d / 4 : ℝ), sq_nonneg (d - 4 / 5 : ℝ)]
  have h2 : d = 4 / 5 := by
    nlinarith

  have h3 : (c - 3 / 5) ^ 2 = 0 := by
    rw [show d = 4 / 5 by linarith [h2]] at h
    nlinarith [sq_nonneg (a - 1 / 5 : ℝ), sq_nonneg (b - 2 / 5 : ℝ), sq_nonneg (c - 3 / 5 : ℝ), sq_nonneg (d - 4 / 5 : ℝ),
          sq_nonneg (a - b / 2 : ℝ), sq_nonneg (b - 2 * c / 3 : ℝ), sq_nonneg (c - 3 * d / 4 : ℝ), sq_nonneg (d - 4 / 5 : ℝ)]
  have h4 : c = 3 / 5 := by
    nlinarith

  have h5 : (b - 2 / 5) ^ 2 = 0 := by
    rw [show c = 3 / 5 by linarith [h4], show d = 4 / 5 by linarith [h2]] at h
    nlinarith [sq_nonneg (a - 1 / 5 : ℝ), sq_nonneg (b - 2 / 5 : ℝ), sq_nonneg (c - 3 / 5 : ℝ), sq_nonneg (d - 4 / 5 : ℝ),
          sq_nonneg (a - b / 2 : ℝ), sq_nonneg (b - 2 * c / 3 : ℝ), sq_nonneg (c - 3 * d / 4 : ℝ), sq_nonneg (d - 4 / 5 : ℝ)]
  have h6 : b = 2 / 5 := by
    nlinarith

  have h7 : (a - 1 / 5) ^ 2 = 0 := by
    rw [show b = 2 / 5 by linarith [h6], show c = 3 / 5 by linarith [h4], show d = 4 / 5 by linarith [h2]] at h
    nlinarith [sq_nonneg (a - 1 / 5 : ℝ), sq_nonneg (b - 2 / 5 : ℝ), sq_nonneg (c - 3 / 5 : ℝ), sq_nonneg (d - 4 / 5 : ℝ),
          sq_nonneg (a - b / 2 : ℝ), sq_nonneg (b - 2 * c / 3 : ℝ), sq_nonneg (c - 3 * d / 4 : ℝ), sq_nonneg (d - 4 / 5 : ℝ)]
  have h8 : a = 1 / 5 := by
    nlinarith

  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith