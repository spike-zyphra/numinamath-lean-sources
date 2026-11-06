import Mathlib

theorem algebra_180033 : 143 * 91 * 77 - Real.sqrt 143 * Real.sqrt 91 * Real.sqrt 77 = 1001000 := by
  -- Use approx nlinarith with facts to profe goal
  have h1 : Real.sqrt 143 * Real.sqrt 91 * Real.sqrt 77 = Real.sqrt (143 * 91 * 77 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  have h2 : Real.sqrt (143 * 91 * 77 : ℝ) = 1001 := by 
    -- Calculate product, verify sqrt
    have h3 : (143 * 91 * 77 : ℝ) = (1002001 : ℝ) := by norm_num
    rw [h3]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  -- Use h relations computationally for Lean to reach goal
  rw [h1, h2]
  all_goals norm_num
  <;> nlinarith