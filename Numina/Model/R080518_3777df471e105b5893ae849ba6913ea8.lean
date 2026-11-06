import Mathlib

theorem algebra_109733 (a b c : ℝ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : a^2 = b^2 + b * c) (h₃ : b^2 = c^2 + a * c) :
    1 / c = 1 / a + 1 / b := by 
  have h4 : 0 < a * b := mul_pos (by linarith) (by linarith)
  have h5 : a * b = c * (a + b) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

  have h6 : 1 / c = 1 / a + 1 / b := by
    field_simp [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
    nlinarith [h5]
  exact h6