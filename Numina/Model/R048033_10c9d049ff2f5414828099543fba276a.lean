import Mathlib

open Finset Complex Polynomial

theorem algebra_184140 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h1 : a 1 = 1) (h2 : ∀ n, (n + 1) * (a n)^2 - 2 * n * (a (n + 1))^2 +
      Real.sqrt (n^2 + n) * a n * a (n + 1) = 0) :
    ‖∏ k ∈ Icc 1 2019, (1 - I / a k) - ∏ k ∈ Icc 1 2020, (1 - I / a k)‖ = 1 := by

  have h3 := h2 0
  have h4 : (0 + 1) * (a 0)^2 - 2 * 0 * (a 1)^2 + Real.sqrt (0^2 + 0) * a 0 * a 1 = 0 := by
    simpa using h3

  have eq_a0 : a 0 = 0 := by
    have h5 : (0 + 1 : ℝ) * a 0 ^ 2 - (2 * (0 : ℝ) * a 1 ^ 2) + Real.sqrt (0 ^ 2 + (0 : ℝ)) * a 0 * a 1 = (0 : ℝ) := by
      simpa using h4

    have h6 : Real.sqrt ((0 : ℝ) ^ 2 + (0 : ℝ)) = (0 : ℝ) := by
      norm_num [Real.sqrt_eq_zero]
    
    rw [h6] at h5
    have h7 : a 0 ^ 2 = (0 : ℝ) := by
      nlinarith
  
    have h8 : a 0 = (0 : ℝ) := by
      nlinarith
  
    exact h8
  
  have h11 : 0 < a 0 := ha 0
  rw [eq_a0] at h11 
  all_goals linarith