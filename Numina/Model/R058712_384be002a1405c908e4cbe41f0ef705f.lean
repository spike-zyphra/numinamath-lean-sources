import Mathlib

open Real

theorem algebra_254644 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 4 * logb 2 x ^ 2 + 1 = 2 * logb 2 y) (h2 : logb 2 (x ^ 2) ≥ logb 2 y) :
    x = sqrt 2 ∧ y = 2 := by
  have h4 : logb 2 (x ^ 2) = 2 * logb 2 x := by
    simp [logb_pow]
  have h2' : 2 * logb 2 x ≥ logb 2 y := by linarith [h2, h4]
  have eq1 : logb 2 y = 2 * (logb 2 x) ^ 2 + 1 / 2 := by 
    nlinarith [h1]
  have h3 : 2 * logb 2 x ≥ 2 * (logb 2 x) ^ 2 + 1 / 2 := by 
    linarith [h2', eq1]
  have h4 : (2 * logb 2 x - 1) ^ 2 ≤ 0 := by 
    nlinarith [h3]
  have h5 : (2 * logb 2 x - 1) ^ 2 = 0 := by 
    nlinarith [h4, sq_nonneg (2 * logb 2 x - 1)]
  have h6 : 2 * logb 2 x - 1 = 0 := by 
    rw [sq_eq_zero_iff] at h5 
    exact h5 
  have hx1 : logb 2 x = 1 / 2 := by
    linarith 
  have hx2 : x = Real.sqrt 2 := by
    have hx_eq : x = (2 : ℝ) ^ (Real.logb 2 x : ℝ) := by 
      field_simp [hx]
    rw [hx_eq]
    rw [hx1]
    rw [Real.sqrt_eq_rpow]
    all_goals norm_num 
  have hy1 : logb 2 y = 1 := by 
    rw [hx1] at eq1 
    nlinarith 
  have hy2 : y = 2 := by 
    have hy_eq : y = (2 : ℝ) ^ (Real.logb 2 y : ℝ) := by 
      field_simp [hy]
    rw [hy_eq]
    rw [hy1]
    all_goals norm_num 
  exact ⟨hx2, hy2⟩