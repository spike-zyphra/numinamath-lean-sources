import Mathlib

theorem inequalities_35054 (a b c : ℝ) (h₀ : a + b > c) (h₁ : a + c > b) (h₂ : b + c > a) :
    2*(a + b + c)*(a^2 + b^2 + c^2)/3 > a^3 + b^3 + c^3 + a*b*c := by
  have h3 : a > 0 := by linarith
  have h4 : b > 0 := by linarith
  have h5 : c > 0 := by linarith

  suffices 2*(a + b + c)*(a^2 + b^2 + c^2) > 3*(a^3 + b^3 + c^3 + a*b*c) by
    linarith
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
            mul_pos h3 h4, mul_pos h3 h5, mul_pos h4 h5]