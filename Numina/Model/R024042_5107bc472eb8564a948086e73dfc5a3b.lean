import Mathlib

theorem algebra_21326 (x y : ℝ) (h : x ^ 2 + 6 * x + y ^ 2 - 12 * y - 4 = 0) :
    Real.sqrt ((x + 3) ^ 2 + (y - 6) ^ 2) * 2 * Real.pi = 14 * Real.pi := by
  have h1 : (x + 3) ^ 2 + (y - 6) ^ 2 = 49 := by
    nlinarith
  have h2 : Real.sqrt ((x + 3) ^ 2 + (y - 6) ^ 2) = 7 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h2]
  all_goals
    linarith [Real.pi_pos]