import Mathlib

theorem algebra_295048 (x : ℝ) (hx : x > 0) (h : 400 + x * 24 = 400 - 120 * Real.sqrt (6 * 24)) :
    x = 40 := by
  have h1 : Real.sqrt (6 * 24 : ℝ) = 12 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith
  rw [h1] at h
  nlinarith