import Mathlib

theorem algebra_195063 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h₁ : Real.logb 10 (x / 2) = 0.5) (h₂ : Real.logb 10 (y / 5) = 0.1) :
    Real.logb 10 (x * y) = 1.6 := by
  have eq1 : Real.logb 10 (x / 2) = Real.logb 10 x - Real.logb 10 2 := by
    rw [Real.logb_div (by linarith) (by norm_num)]
  have eq2 : Real.logb 10 (y / 5) = Real.logb 10 y - Real.logb 10 5 := by
    rw [Real.logb_div (by linarith) (by norm_num)]
  rw [eq1] at h₁
  rw [eq2] at h₂
  have eq3 : Real.logb 10 (x * y) = Real.logb 10 x + Real.logb 10 y := by
    rw [Real.logb_mul (by linarith) (by linarith)]
  have h3 : Real.logb 10 x = 0.5 + Real.logb 10 2 := by
    linarith 
  have h4 : Real.logb 10 y = 0.1 + Real.logb 10 5 := by
    linarith
  rw [eq3]
  rw [h3, h4]
  have h5 : Real.logb 10 2 + Real.logb 10 5 = 1 := by
    calc 
      Real.logb 10 2 + Real.logb 10 5 = Real.logb 10 (2 * 5) := by
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      _ = Real.logb 10 10 := by
        norm_num 
      _ = 1 := by
        norm_num [Real.logb_eq_iff_rpow_eq]
  have h6 : (0.5 + Real.logb 10 2) + (0.1 + Real.logb 10 5) = 1.6 := by
    calc 
      (0.5 + Real.logb 10 2) + (0.1 + Real.logb 10 5) = 0.6 + (Real.logb 10 2 + Real.logb 10 5) := by 
        ring 
      _ = 0.6 + (1 : ℝ) := by 
        rw [h5]
      _ = (1.6 : ℝ) := by 
        norm_num 
  norm_num at h6 ⊢
  linarith