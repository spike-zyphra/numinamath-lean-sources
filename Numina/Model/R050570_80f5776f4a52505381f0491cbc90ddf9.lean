import Mathlib

theorem algebra_221069 {x : ℝ} (hx : x > 0) (h : Real.logb 2 x = Real.logb 4 (2 * x) + Real.logb 8 (4 * x)) :
    x = 128 := by
  have h1 : Real.logb 4 (2 * x) = (Real.logb 2 (2 * x)) / (Real.logb 2 (4 : ℝ)) := by
    field_simp [Real.logb]
  have h2 : Real.logb 8 (4 * x) = (Real.logb 2 (4 * x)) / (Real.logb 2 (8 : ℝ)) := by
    field_simp [Real.logb]
  have h3 : Real.logb 2 (2 * x) = Real.logb 2 (2 : ℝ) + Real.logb 2 x := by 
    rw [Real.logb_mul (by norm_num) (by linarith)]
  have h4 : Real.logb 2 (2 : ℝ) = 1 := by 
    simp [Real.logb_self_eq_one]
  have h5 : Real.logb 2 (4 * x) = Real.logb 2 (4 : ℝ) + Real.logb 2 x := by 
    rw [Real.logb_mul (by norm_num) (by linarith)]
  have h6 : Real.logb 2 (4 : ℝ) = 2 := by 
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  have h7 : Real.logb 2 (8 : ℝ) = 3 := by 
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  have eq1 : Real.logb 4 (2 * x) = (1 + Real.logb 2 x) / 2 := by 
    rw [h1]
    rw [h3, h4, h6]
    <;> ring_nf <;> linarith
  have eq2 : Real.logb 8 (4 * x) = (2 + Real.logb 2 x) / 3 := by 
    rw [h2]
    rw [h5, h6, h7]
    <;> ring_nf <;> linarith
  rw [eq1, eq2] at h 
  have h8 : Real.logb 2 x = 7 := by 
    linarith
  have hx2 : x = (2 : ℝ) ^ (7 : ℝ) := by
    have h9 : Real.logb 2 x = 7 := h8
    have h10 : x = (2 : ℝ) ^ (Real.logb 2 x) := by 
      field_simp [Real.rpow_logb, show (2 : ℝ) > 0 by norm_num, show (2 : ℝ) ≠ 1 by norm_num, hx]
    rw [h10, h9]
  norm_num at hx2 ⊢
  exact hx2