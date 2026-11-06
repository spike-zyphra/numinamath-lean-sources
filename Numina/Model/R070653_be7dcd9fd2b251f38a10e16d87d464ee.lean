import Mathlib

theorem algebra_5979 (y : ℝ) (h : y < 0) : -Real.sqrt (0.25 * y^2) = y / 2 := by
  have h5 : Real.sqrt (0.25 * y^2) = - (y / 2) := by
    have h2 : Real.sqrt (0.25 * y^2) = (Real.sqrt (0.25 : ℝ)) * Real.sqrt (y^2) := by
      rw [Real.sqrt_mul (by positivity)]
    have h3 : Real.sqrt (0.25 : ℝ) = 0.5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt (y^2) = - y := by 
      have : Real.sqrt (y^2) = abs y := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [this]
      rw [abs_of_neg h]
      all_goals linarith
    rw [h2, h3, h4]
    ring_nf
  rw [h5]
  all_goals linarith
  all_goals linarith