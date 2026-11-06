import Mathlib

theorem algebra_11965 {r : ℝ} (hr : (r + 16) > 0) (h : Real.logb 16 (r + 16) = 5 / 4) :
    r = 16 := by
  have h1 : (r + 16) = (16 : ℝ) ^ (5 / 4 : ℝ) := by
    rw [← h]
    field_simp [Real.rpow_logb, show (16 : ℝ) > 0 by norm_num, show (16 : ℝ) ≠ 1 by norm_num, show (r + 16) > 0 by assumption
    ]
    all_goals linarith
  have h2 : (16 : ℝ) ^ (5 / 4 : ℝ) = 32 := by
    have h3 : (16 : ℝ) ^ (5 / 4 : ℝ) = ((2 : ℝ) ^ (4 : ℝ)) ^ (5 / 4 : ℝ) := by norm_num
    rw [h3]
    rw [← Real.rpow_mul ]
    norm_num
    norm_num
    all_goals norm_num
  rw [h2] at h1
  have hr2 : r = 16 := by
    linarith
  exact hr2