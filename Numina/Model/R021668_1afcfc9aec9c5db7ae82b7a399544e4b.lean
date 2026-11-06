import Mathlib

open Real

theorem algebra_194473 : logb (1/4) (1/2) = 1/2 := by 
  rw [logb]
  have h1 : log (1 / 2) = -log (2 : ℝ) := by 
    rw [log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 : log (1 / 4) = -2 * log (2 : ℝ) := by
    calc
      log (1 / 4) = log (1) - log (4 : ℝ) := by
        rw [log_div (by norm_num) (by norm_num)]
        all_goals norm_num
      _ = 0 - log (4 : ℝ) := by 
        simp 
      _ = 0 - 2 * log (2 : ℝ) := by
        have h3 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
          calc 
            log (4 : ℝ) = log (2 ^ 2) := by norm_num
            _ = 2 * log (2 : ℝ) := by simp [log_pow]
        rw [h3]
      _ = -2 * log (2 : ℝ) := by 
        ring
  rw [h1, h2]
  have h3 : log (2 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals linarith
  field_simp [show log (2 : ℝ) ≠ 0 by linarith]
  <;> ring_nf <;> field_simp [show log (2 : ℝ) ≠ 0 by linarith]
  <;> linarith