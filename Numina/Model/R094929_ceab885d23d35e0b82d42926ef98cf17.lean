import Mathlib

theorem algebra_195869 : Real.logb 3 12 = Real.logb 3 7 * Real.logb 7 5 * Real.logb 5 4 + 1 := by
  have h1 : Real.logb 3 12 = Real.logb 3 (3 * 4) := by
    norm_num
  have h2 : Real.logb 3 (3 * 4) = Real.logb 3 3 + Real.logb 3 4 := by
    rw [Real.logb_mul (by norm_num) (by norm_num)]
  have h3 : Real.logb 3 3 = 1 := by
    rw [Real.logb_self_eq_one]
    all_goals norm_num
  have h10 : Real.logb 3 12 = Real.logb 3 4 + 1 := by
    rw [h1, h2, h3]
    all_goals linarith
  have h4 : Real.logb 3 7 * Real.logb 7 5 * Real.logb 5 4 = Real.logb 3 4 := by
    have h5 : Real.logb 3 7 * Real.logb 7 5 = Real.logb 3 5 := by
      field_simp [Real.logb]
      <;> ring_nf <;> simp [Real.logb, Real.log_one]
      <;> ring
    calc
      Real.logb 3 7 * Real.logb 7 5 * Real.logb 5 4
        = (Real.logb 3 7 * Real.logb 7 5) * Real.logb 5 4 := by ring
      _ = Real.logb 3 5 * Real.logb 5 4 := by rw [h5]
      _ = Real.logb 3 4 := by 
        field_simp [Real.logb]
        <;> ring_nf <;> simp [Real.logb, Real.log_one]
        <;> ring
  linarith [h10, h4]
  all_goals norm_num