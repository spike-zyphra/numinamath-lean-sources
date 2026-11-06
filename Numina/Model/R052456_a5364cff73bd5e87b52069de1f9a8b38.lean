import Mathlib

theorem inequalities_5009 (a b : ℝ) (h₀ : abs (3 * a ^ 2 - 1) ≤ 2 * b) (h₁ : abs (3 * b ^ 2 - 2) ≤ a) :
    a ^ 4 + b ^ 3 ≤ 2 := by
  have h2 : -2 * b ≤ 3 * a ^ 2 - 1 := by linarith [abs_le.mp h₀]
  have h3 : 3 * a ^ 2 - 1 ≤ 2 * b := by linarith [abs_le.mp h₀]
  have h4 : -a ≤ 3 * b ^ 2 - 2 := by linarith [abs_le.mp h₁]
  have h5 : 3 * b ^ 2 - 2 ≤ a := by linarith [abs_le.mp h₁]
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), 
          sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (b + 1), 
          sq_nonneg (a - b), sq_nonneg (3 * a ^ 2 - 1 - 2 * b), 
          sq_nonneg (3 * b ^ 2 - 2 - a)]