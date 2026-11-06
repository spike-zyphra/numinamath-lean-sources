import Mathlib

theorem algebra_186395 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c > 0) :
    a * b + b * c + c * a < 0 := by 
  have h2 : c = -a - b := by linarith
  rw [h2] at h₁ 
  rw [h2]
  have h3 : a ^ 2 + b ^ 2 + a * b > 0 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b), sq_pos_of_pos (show 0 < (1 : ℝ) by norm_num), sq_nonneg (a * (b)), sq_nonneg ((a + b) * b), sq_nonneg (a * b * (a + b)), mul_pos (show (0 : ℝ) < (1 : ℝ) by norm_num) (show (0 : ℝ) < (1 : ℝ) by norm_num)]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a * (b)), sq_nonneg ((a + b) * b), sq_nonneg (a * b * (a + b))]