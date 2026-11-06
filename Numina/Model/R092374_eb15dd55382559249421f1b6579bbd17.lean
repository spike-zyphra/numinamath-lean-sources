import Mathlib

theorem algebra_303254 {a b c : ℝ} (h₀ : a - b = 5 + Real.sqrt 6) (h₁ : b - c = 5 - Real.sqrt 6) :
    a^2 + b^2 + c^2 - a * b - b * c - c * a = 81 := by
  have h2 : a - c = 10 := by
    have h3 : a - c = (a - b) + (b - c) := by linarith
    rw [h3, h₀, h₁]
    ring
  have h3 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 162 := by
    have h4 : c - a = -10 := by linarith [h2]
    rw [h4, h₀, h₁]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
           Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), h3]