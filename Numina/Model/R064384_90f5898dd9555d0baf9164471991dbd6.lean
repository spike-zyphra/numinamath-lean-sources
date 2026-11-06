import Mathlib

theorem algebra_281553 {x : ℝ} (hx : x = 4) : √x / 2 = 1 := by
  rw [hx]
  have h1 : √(4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  norm_num