import Mathlib

theorem algebra_174273 {a b : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x^2 + (a^2 + b^2 - 1)*x + a^2 + 2*a*b - b^2)
    (h₁ : ∀ x, f (-x) = f x) :
    f 0 ≤ Real.sqrt 2 := by
  have h2 := h₁ 1
  rw [h₀, h₀] at h2
  have h4 : a ^ 2 + b ^ 2 = 1 := by
    nlinarith 
  have h5 : f 0 = a^2 + 2 * a * b - b^2 := by
    rw [h₀]
    all_goals
      norm_num
  rw [h5] 
  nlinarith [sq_nonneg (a - (Real.sqrt 2 / 2) - b), sq_nonneg (a + (Real.sqrt 2 / 2) - b), 
          sq_nonneg (a - (1 + Real.sqrt 2) * b), sq_nonneg (a - (1 - Real.sqrt 2) * b), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
          sq_nonneg (b^2 - (2 - Real.sqrt 2)/4), sq_nonneg (a - (Real.sqrt 2)/2), sq_nonneg (b - (Real.sqrt 2)/2), sq_nonneg (a - b) 
        ]