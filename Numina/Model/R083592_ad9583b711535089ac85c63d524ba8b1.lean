import Mathlib

theorem algebra_325003 {a b c : ℝ} (h₀ : a + b + c = 3) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 3) :
    a ^ 2003 + b ^ 2003 + c ^ 2003 = 3 := by 
  have h2 : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 = 0 := by 
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