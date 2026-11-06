import Mathlib

theorem algebra_112950 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a = Real.logb 0.1 b) :
    Real.logb 10 (b^a) = -a^2 := by
  have h1 : Real.logb 0.1 b = Real.logb 10 b / Real.logb 10 (0.1 : ℝ) := by
    field_simp [Real.logb]
    all_goals linarith
  have h2 : Real.logb 10 (0.1 : ℝ) = -1 := by 
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    <;> linarith
  rw [h1] at h
  rw [h2] at h
  have h3 : Real.logb 10 b = -a := by
    field_simp at h ⊢
    linarith
  have h4 : Real.logb 10 (b ^ a) = a * Real.logb 10 b := by 
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  rw [h4]
  rw [h3]
  <;> nlinarith [sq_nonneg a]