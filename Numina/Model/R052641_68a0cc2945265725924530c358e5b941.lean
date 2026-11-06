import Mathlib

theorem algebra_10583 {x : ℝ} (hx : x > 4) (h : Real.logb 25 (x - 4) = 1 / 2) :
    1 / Real.logb x 3 = 2 := by
  have h1 : x - 4 = (25 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.logb_eq_iff_rpow_eq] at h
    · linarith
    all_goals linarith
  have h2 : (25 : ℝ) ^ (1 / 2 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have hx_val : x = 9 := by
    have h3 : x - 4 = 5 := by
      rw [h2] at h1
      linarith
    linarith
  rw [hx_val]
  have h4 : Real.logb 9 3 = Real.log 3 / Real.log 9 := by 
    field_simp [Real.logb]
  have h5 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h6 : 1 / Real.logb 9 3 = 2 := by
    rw [h4]
    have h7 : Real.log 3 ≠ 0 := by
      have h8 : Real.log 3 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    field_simp [h5, h7]
    <;> ring
  exact h6