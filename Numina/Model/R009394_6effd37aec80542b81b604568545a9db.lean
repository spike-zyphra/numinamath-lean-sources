import Mathlib

theorem algebra_16548 : √25000 = 50 * √10 := by
  calc
    √25000 = √(50^2 * 10) := by norm_num
    _ = (50 : ℝ) * √10 := by
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      all_goals norm_num