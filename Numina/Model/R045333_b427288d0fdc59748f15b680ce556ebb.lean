import Mathlib

theorem algebra_62923 {a b c d : ℝ} (h : a^2 + b^2 + (a + b)^2 = c^2 + d^2 + (c + d)^2) :
    a^4 + b^4 + (a + b)^4 = c^4 + d^4 + (c + d)^4 := by
  have eq1 : a^2 + b^2 + a * b = c^2 + d^2 + c * d := by
    have h1 : a^2 + b^2 + (a + b) ^ 2 = 2 * (a^2 + b^2 + a * b) := by 
      ring
    have h2 : c^2 + d^2 + (c + d) ^ 2 = 2 * (c^2 + d^2 + c * d) := by 
      ring
    have h3 : 2 * (a^2 + b^2 + a * b) = 2 * (c^2 + d^2 + c * d) := by
      linarith [h, h1, h2]
    linarith
  nlinarith [sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - d^2), sq_nonneg (a * b - c * d), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + b - (c + d)), sq_nonneg (a * b - c * d), sq_nonneg (a^2 + b^2 - c^2 - d^2), eq1]