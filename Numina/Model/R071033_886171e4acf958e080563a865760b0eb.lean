import Mathlib

theorem algebra_10631 {x : ℝ} (hx : x > 0) (h : Real.logb 6 (4 * x) = 2) :
    Real.logb x 27 = 3 / 2 := by
  have h1 : 4 * x = (6 : ℝ) ^ (2 : ℝ) := by
    have h2 : 4 * x > 0 := by
      nlinarith
    have h3 : (6 : ℝ) ^ (Real.logb 6 (4 * x)) = (4 * x) := by
      field_simp [Real.rpow_logb, show (6 : ℝ) > 0 by norm_num, show (6 : ℝ) ≠ 1 by norm_num, h2]
    rw [h] at h3
    nlinarith
  have hx_eq : x = 9 := by
    nlinarith
  rw [hx_eq]
  have h4 : Real.logb (9 : ℝ) 27 = 3 / 2 := by
    rw [Real.logb]
    have h5 : Real.log (27 : ℝ) = 3 * Real.log (3 : ℝ) := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    have h6 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    rw [h5, h6]
    have h7 : Real.log (3 : ℝ) > 0 := by
      apply Real.log_pos
      norm_num
    field_simp [h7]
    all_goals linarith
  exact h4