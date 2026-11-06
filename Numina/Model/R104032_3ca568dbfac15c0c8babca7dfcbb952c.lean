import Mathlib

theorem algebra_2711 {a b c : ℝ} (h₀ : a^2 - b^2 = 1 + Real.sqrt 2) (h₁ : b^2 - c^2 = 1 - Real.sqrt 2) :
    a^4 + b^4 + c^4 - a^2 * b^2 - b^2 * c^2 - c^2 * a^2 = 5 := by
  have h2 : a^2 - c^2 = 2 := by 
    nlinarith [h₀, h₁, Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  
  have eq1 : a^2 = b^2 + 1 + Real.sqrt 2 := by linarith
  have eq2 : c^2 = b^2 - 1 + Real.sqrt 2 := by
    nlinarith [h₀, h₁, Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  
  nlinarith [sq_nonneg (b^2 - 1), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (a^2 - b^2 - 1 - Real.sqrt 2), sq_nonneg (b^2 - c^2 - 1 + Real.sqrt 2), sq_nonneg (a^2 - c^2 - 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]