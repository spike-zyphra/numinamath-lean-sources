import Mathlib

theorem algebra_219694 {a b : ℝ} (ha : a = Real.logb 8 225) (hb : b = Real.logb 2 15) :
    a = 2 * b / 3 := by
  rw [ha, hb]
  have h1 : Real.logb 8 225 = Real.logb 2 225 / Real.logb 2 8 := by
    field_simp [Real.logb]
    all_goals norm_num
  have h2 : Real.logb 2 8 = 3 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  have h3 : Real.logb 2 225 = 2 * Real.logb 2 15 := by
    have h4 : (225 : ℝ) = (15 : ℝ) ^ 2 := by norm_num
    rw [h4]
    simp [Real.logb_pow]
    all_goals norm_num
  rw [h1, h2, h3]
  all_goals ring