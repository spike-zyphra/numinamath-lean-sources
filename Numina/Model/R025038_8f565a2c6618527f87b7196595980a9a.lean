import Mathlib

theorem algebra_146816 (x y : ℝ) (h₁ : 3 * x ≥ 2 * y + 16) (h₂ : x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4 + 25 - 26 * x ^ 2 - 26 * y ^ 2 = 72 * x * y) :
    (x, y) = (6, 1) := by
  have h3 : (x - 6) ^ 2 + (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 - 36), sq_nonneg (y^2 - 1), sq_nonneg (x - 6), sq_nonneg (y - 1), 
      sq_nonneg (x * y - 6), sq_nonneg (3 * x - 2 * y - 16), h₁]
  have hx : x - 6 = 0 := by
    nlinarith [h3]
  have hy : y - 1 = 0 := by
    nlinarith [h3]
  have hx2 : x = 6 := by linarith
  have hy2 : y = 1 := by linarith
  simp [Prod.ext_iff, hx2, hy2]