import Mathlib

theorem algebra_136138 : Real.sqrt (0.04 ^ 3) = 1 / 125 := by
  have h2 : (0.04 : ℝ) ^ 3 = (1 / 15625 : ℝ) := by
    norm_num
  rw [h2]
  have h3 : Real.sqrt ( (1 / 15625 : ℝ) ) = (1 / 125 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  exact h3