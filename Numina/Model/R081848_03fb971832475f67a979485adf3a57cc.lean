import Mathlib

theorem inequalities_600063 (θ : ℝ) : 5 + 8 * Real.cos θ + 4 * Real.cos (2 * θ) + Real.cos (3 * θ) ≥ 0 := by 
  have h1 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h2 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := by
    rw [Real.cos_three_mul]
  rw [h1, h2]
  nlinarith [sq_nonneg (Real.cos θ - 1), sq_nonneg (Real.cos θ + 1), sq_nonneg (2 * Real.cos θ + 1),
          Real.cos_sq_add_sin_sq θ, sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]