import Mathlib

theorem algebra_319084 {a b c : ℝ} (h₀ : a + b + c = 3) (h₁ : a^2 + b^2 + c^2 = 3) :
    a^2005 + b^2005 + c^2005 = 3 := by
  have h2 : a * b + b * c + c * a = 3 := by
    have h2 : (a + b + c)^2 = 9 := by
      rw [h₀]
      norm_num
    have h3 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
      ring
    rw [h₁] at h3
    nlinarith
  have h3 : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 = 0 := by
    nlinarith
  have ha : a - 1 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have hb : b - 1 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have hc : c - 1 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have ha1 : a = 1 := by linarith
  have hb1 : b = 1 := by linarith
  have hc1 : c = 1 := by linarith
  rw [ha1, hb1, hc1]
  norm_num