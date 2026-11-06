import Mathlib

theorem algebra_195299 (x : ℝ) (hx : x = 0) :
    6.280 * Real.sqrt x - Real.sqrt (x + 1) - Real.sqrt (x + 4) + Real.sqrt (x + 9) = 0 := by 
  rw [hx]
  have h1 : Real.sqrt (0 : ℝ) = 0 := by
    simp [Real.sqrt_eq_zero]
  have h2 : Real.sqrt (1 : ℝ) = 1 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : Real.sqrt (9 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  simp only [h1, show Real.sqrt (0 + 1 : ℝ) = Real.sqrt (1 : ℝ) by ring, h2, 
          show Real.sqrt (0 + 4 : ℝ) = Real.sqrt (4 : ℝ) by ring, h3, 
          show Real.sqrt (0 + 9 : ℝ) = Real.sqrt (9 : ℝ) by ring, h4]
  all_goals norm_num