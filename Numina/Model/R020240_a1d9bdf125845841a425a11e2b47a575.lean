import Mathlib

open Real

theorem algebra_291404 {x : ℝ} (hx : x = (logb 8 2) ^ (logb 2 8)) : logb 3 x = -3 := by
  have h1 : logb 8 2 = 1 / 3 := by 
    rw [logb]
    have h2 : log 8 = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
      simp [log_pow]
      all_goals linarith
    field_simp [h2]
    <;> ring_nf <;> field_simp <;> linarith
  have h3 : logb 2 8 = 3 := by
    rw [logb]
    have h4 : log 8 = 3 * log 2 := by 
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
      simp [log_pow]
      all_goals linarith
    field_simp [h4]
    <;> ring_nf <;> field_simp <;> linarith
  have h2 : x = (1 / 27 : ℝ) := by
    rw [hx]
    rw [h1, h3]
    norm_num
  rw [h2]
  have h5 : logb 3 (1 / 27 : ℝ) = -3 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  exact h5