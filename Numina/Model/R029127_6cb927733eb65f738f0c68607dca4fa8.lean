import Mathlib

theorem algebra_274805 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : b = a * c) (h₄ : a + b + c = 35) (h₅ : Real.logb 10 a + Real.logb 10 b + Real.logb 10 c = 3) :
    max (max a b) c = 20 := by
  have h6 : a * b * c = 1000 := by
    have h7 : Real.logb 10 (a * b * c) = Real.logb 10 a + Real.logb 10 b + Real.logb 10 c := by
      have h9 : Real.logb 10 (a * b * c) = Real.logb 10 (a * b) + Real.logb 10 c := by
        rw [Real.logb_mul]
        all_goals nlinarith [h₀, h₁, h₂]
      have h10 : Real.logb 10 (a * b) = Real.logb 10 a + Real.logb 10 b := by
        rw [Real.logb_mul]
        all_goals nlinarith [h₀, h₁, h₂]
      rw [h9, h10]
      all_goals linarith
    have h8 : Real.logb 10 (a * b * c) = 3 := by
      linarith [h₅, h7]
    have h15 : a * b * c = (10 : ℝ) ^ (3 : ℝ) := by
      rw [←h8]
      field_simp [Real.rpow_logb, show (10 : ℝ) > 0 by norm_num, show (10 : ℝ) ≠ 1 by norm_num, show (10 : ℝ) > 1 by norm_num]
      all_goals nlinarith [h₀, h₁, h₂, h₃, h₄]
    rw [h15]
    norm_num
  rw [h₃] at h₄ h6
  have h7 : a = 10 := by
    nlinarith [sq_nonneg (a - 10), sq_nonneg (b - 20), sq_nonneg (c - 5), h₀, h₁, h₂, h₄, h6]
  have h8 : b = 20 := by
    nlinarith [h7, h₄]
  have h9 : c = 5 := by
    nlinarith [h7, h₄]
  rw [h7, h8, h9]
  norm_num [max_eq_right, max_eq_left]
  all_goals linarith
  all_goals nlinarith
  all_goals linarith