import Mathlib

theorem algebra_312892 {a b c d : ℝ} (h₀ : 2*a^2 + 3*c^2 = 6) (h₁ : 2*b^2 + 3*d^2 = 6)
    (h₂ : (a*d - b*c)^2 = 6) : (a^2 + b^2)*(c^2 + d^2) = 6 := by

  have h3 : (2*a^2 + 3*c^2) * (2*b^2 + 3*d^2) = 36 := by
    rw [show (2*a^2 + 3*c^2) = 6 by linarith [h₀]]
    rw [show (2*b^2 + 3*d^2) = 6 by linarith [h₁]]
    norm_num

  have h4 : 4*a^2*b^2 + 6*a^2*d^2 + 6*b^2*c^2 + 9*c^2*d^2 = 36 := by
    linarith [h3]

  have h5 : (2*a*b + 3*c*d)^2 = 0 := by
    have h6 : a^2*d^2 + b^2*c^2 = 6 + 2*(a*b*c*d) := by
      nlinarith [h₂]
    nlinarith [h4, h6]

  have h7 : 2*a*b + 3*c*d = 0 := by 
    nlinarith [h5]

  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c + b*d), sq_nonneg (a*d - b*c), sq_nonneg (a^2 + b^2 - 3), sq_nonneg (c^2 + d^2 - 2), mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (a * b + c * d)]