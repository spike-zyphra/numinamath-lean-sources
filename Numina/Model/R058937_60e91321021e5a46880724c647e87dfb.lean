import Mathlib

theorem algebra_275969 {a b c : ℝ} (h : a + b + c = 0) :
    2*(a^4+b^4+c^4) = (a^2+b^2+c^2)^2 := by
  have h1 : c = -(a + b) := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_nonneg (a * b)]